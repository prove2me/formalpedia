-- Prove2me | Theorems.Thm_QDSGibbs_proposition_5_7
-- name    : QDSGibbs.proposition_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:08.753938+00:00
-- url     : https://prove2.me/theorems/e47c31d4-3957-49e4-9e36-39adc96754a9
-- title:
--   Proposition 5.7 — locality of the block generators and channels in diamond norm
-- statement:
--   On a nearest-neighbour chain with local dimensions $2\le d_i\le d$, with the same $\lambda$ and a constant $C_d<\infty$,
--
--   $$
--   \|\mathcal K_B\|_\diamond,\ \|\mathcal K_{B,u}\|_\diamond\le q_\beta:=C_de^{2\beta J_{\mathrm{int}}}(1+\beta J_{\mathrm{int}})^4\log(2+\beta J_{\mathrm{int}}),
--   $$
--
--   $$
--   \|\mathcal K_B-\mathcal K_{B,u}\|_\diamond\le q_\beta e^{-\lambda u/2},\qquad \|\Phi_B(T)-\Phi_{B,u}(T)\|_\diamond\le q_\beta Te^{-\lambda u/2},
--   $$
--
--   for every interval $B$, integer $u\ge0$ and $T\ge0$. The same bounds hold after tensoring the maps with the identity on an arbitrary finite-dimensional reference system.
--
--   **Formalization Note** The last sentence is contained in the statement: the diamond norm is a supremum over all reference dimensions, so tensoring with a further identity does not change it.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: "$C_d$ depends only on $d$" → $C_d$ chosen after the local-dimension bound `dmax` ($2\le d_i\le$ `dmax`) and before everything else; reason: the paper's convention on p.39
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - encoding: "the same bounds hold after tensoring the maps with the identity on an arbitrary finite-dimensional reference system" → not stated as a separate clause; reason: `diamondNorm` is a supremum over every reference dimension $m\ge1$ and $(F\otimes\mathrm{id}_k)\otimes\mathrm{id}_m$ is $F\otimes\mathrm{id}_{km}$ up to reordering, so $\|F\otimes\mathrm{id}_k\|_\diamond=\|F\|_\diamond$ and the tensored bounds are the stated ones
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Proposition 5.7, p.44

import Mathlib
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Proposition 5.7** (arXiv:2610.03578, held file sha256 ede55815…, Proposition 5.7, p.44). With
the same `λ` and a constant `C_d < ∞`,
`‖K_B‖⋄, ‖K_{B,u}‖⋄ ≤ q_β := C_d e^{2βJ_int}(1 + βJ_int)^4 log(2 + βJ_int)` (5.14),
`‖K_B − K_{B,u}‖⋄ ≤ q_β e^{−λu/2}` (5.15), `‖Φ_B(T) − Φ_{B,u}(T)‖⋄ ≤ q_β T e^{−λu/2}` (5.16). The same
bounds hold after tensoring the maps with the identity on an arbitrary finite-dimensional reference
system.

**Formalization Note** `λ = c/(1 + βJ_int)` with universal `c ∈ (0, 1]`; `C_d > 0` depends only on
`dmax`; every interval `B`, integer `u ≥ 0`, and (5.16) for every `T ≥ 0`. `K_B = blockGen β I B
univ`, `K_{B,u} = blockGen β I B (C_u(B))` (5.13). The last sentence is contained in the statement:
`diamondNorm` is a supremum over all reference dimensions `m ≥ 1`, and `(F ⊗ id_k) ⊗ id_m` is
`F ⊗ id_{km}` up to reordering, so `‖F ⊗ id_k‖⋄ = ‖F‖⋄`. -/
theorem proposition_5_7 :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ dmax : ℕ, 2 ≤ dmax → ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ B : Finset (Fin N), IsInterval B → ∀ u : ℕ,
            diamondNorm (blockGen β (chain V W) B Finset.univ) ≤
              ENNReal.ofReal (Cd * Real.exp (2 * β * jint (chain V W)) *
                (1 + β * jint (chain V W)) ^ 4 * Real.log (2 + β * jint (chain V W))) ∧
            diamondNorm (blockGen β (chain V W) B (bdryNbhd B u)) ≤
              ENNReal.ofReal (Cd * Real.exp (2 * β * jint (chain V W)) *
                (1 + β * jint (chain V W)) ^ 4 * Real.log (2 + β * jint (chain V W))) ∧
            diamondNorm (fun X => blockGen β (chain V W) B Finset.univ X -
                blockGen β (chain V W) B (bdryNbhd B u) X) ≤
              ENNReal.ofReal (Cd * Real.exp (2 * β * jint (chain V W)) *
                (1 + β * jint (chain V W)) ^ 4 * Real.log (2 + β * jint (chain V W)) *
                Real.exp (-(c / (1 + β * jint (chain V W))) * u / 2)) ∧
            ∀ T : ℝ, 0 ≤ T →
              diamondNorm (fun X => blockChannel β (chain V W) B Finset.univ T X -
                  blockChannel β (chain V W) B (bdryNbhd B u) T X) ≤
                ENNReal.ofReal (Cd * Real.exp (2 * β * jint (chain V W)) *
                  (1 + β * jint (chain V W)) ^ 4 * Real.log (2 + β * jint (chain V W)) * T *
                  Real.exp (-(c / (1 + β * jint (chain V W))) * u / 2)) := by sorry

end QDSGibbs
