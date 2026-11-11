-- Prove2me | Theorems.Thm_QDSGibbs_lemma_5_6
-- name    : QDSGibbs.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:57.2272+00:00
-- url     : https://prove2.me/theorems/438027df-3c78-4650-bb28-936c954c8db3
-- title:
--   Lemma 5.6 — bounds on the coherent terms $G_B$, $G_{B,u}$
-- statement:
--   On a nearest-neighbour chain with local dimensions $2\le d_i\le d$, with $\lambda=c/(1+\beta J_{\mathrm{int}})$ as in Lemma 5.4, $G_B=\mathcal G_H(S_B)$ and $G_{B,u}=\mathcal G_{H_{C_u(B)}}(S_{B,u})$:
--
--   $$
--   \|G_B\|,\ \|G_{B,u}\|\le C_de^{2\beta J_{\mathrm{int}}}(1+\beta J_{\mathrm{int}})^4\log(2+\beta J_{\mathrm{int}}),
--   $$
--
--   $$
--   \|G_B-G_{B,u}\|\le C_de^{2\beta J_{\mathrm{int}}}(1+\beta J_{\mathrm{int}})^4\log(2+\beta J_{\mathrm{int}})\,e^{-\lambda u/2},
--   $$
--
--   for every interval $B$ and integer $u\ge0$, with $C_d$ depending only on $d$.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: "$C_d$ depends only on $d$" → $C_d$ chosen after the local-dimension bound `dmax` ($2\le d_i\le$ `dmax`) and before everything else; reason: the paper's convention on p.39
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 5.6, p.43

import Mathlib
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix

namespace QDSGibbs

/-- **Lemma 5.6** (arXiv:2610.03578, held file sha256 ede55815…, Lemma 5.6, p.43). With
`λ = c/(1 + βJ_int)` as in Lemma 5.4,
`‖G_B‖, ‖G_{B,u}‖ ≤ C_d e^{2βJ_int}(1 + βJ_int)^4 log(2 + βJ_int)` and
`‖G_B − G_{B,u}‖ ≤ C_d e^{2βJ_int}(1 + βJ_int)^4 log(2 + βJ_int) e^{−λu/2}`.

**Formalization Note** `c ∈ (0, 1]` is universal (as in Lemma 5.4); `C_d > 0` depends only on the
local dimension bound `dmax` (`2 ≤ d_i ≤ dmax`). `G_B = gOp β I B univ = G_H(S_B)`,
`G_{B,u} = gOp β I B (C_u(B)) = G_{H_{C_u(B)}}(S_{B,u})` (p.42); every interval `B`, integer `u ≥ 0`. -/
theorem lemma_5_6 :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ dmax : ℕ, 2 ≤ dmax → ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ B : Finset (Fin N), IsInterval B → ∀ u : ℕ,
            opNorm (gOp β (chain V W) B Finset.univ) ≤
              Cd * Real.exp (2 * β * jint (chain V W)) * (1 + β * jint (chain V W)) ^ 4 *
                Real.log (2 + β * jint (chain V W)) ∧
            opNorm (gOp β (chain V W) B (bdryNbhd B u)) ≤
              Cd * Real.exp (2 * β * jint (chain V W)) * (1 + β * jint (chain V W)) ^ 4 *
                Real.log (2 + β * jint (chain V W)) ∧
            opNorm (gOp β (chain V W) B Finset.univ - gOp β (chain V W) B (bdryNbhd B u)) ≤
              Cd * Real.exp (2 * β * jint (chain V W)) * (1 + β * jint (chain V W)) ^ 4 *
                Real.log (2 + β * jint (chain V W)) *
                Real.exp (-(c / (1 + β * jint (chain V W))) * u / 2) := by sorry

end QDSGibbs
