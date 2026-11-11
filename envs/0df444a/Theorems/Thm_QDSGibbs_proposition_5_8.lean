-- Prove2me | Theorems.Thm_QDSGibbs_proposition_5_8
-- name    : QDSGibbs.proposition_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:38:55.933623+00:00
-- url     : https://prove2.me/theorems/d308f469-3c5b-4108-8177-a032912394d9
-- title:
--   Proposition 5.8 — transport-norm approximation of $\Phi_B(T)$ by $\Phi_{B,u}(T)$
-- statement:
--   On a nearest-neighbour chain with local dimensions $2\le d_i\le d$, with $\lambda$ from Proposition 5.7, for every Hermitian $X$, every interval $B$ with $|B|\le\ell$, integer $u\ge0$ and $T\ge0$,
--
--   $$
--   \big\|[\Phi_B(T)-\Phi_{B,u}(T)](X)\big\|_{W_1}\le K_\beta T(\ell+u+2)e^{-\lambda u/2}\|X\|_1,\qquad K_\beta=C_de^{2\beta J_{\mathrm{int}}}(1+\beta J_{\mathrm{int}})^6\log(2+\beta J_{\mathrm{int}}).
--   $$
--
--   This transfers influence bounds from the localized block channels to the exact ones.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: "$C_d$ depends only on $d$" → $C_d$ chosen after the local-dimension bound `dmax` ($2\le d_i\le$ `dmax`) and before everything else; reason: the paper's convention on p.39
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Proposition 5.8, p.44

import Mathlib
import Definitions.Def_QDSGibbs_chainGen
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Proposition 5.8** (arXiv:2610.03578, held file sha256 ede55815…, Proposition 5.8, p.44). With
`λ` from Proposition 5.7, for every Hermitian `X` and `|B| ≤ ℓ`,
`‖[Φ_B(T) − Φ_{B,u}(T)](X)‖_{W1} ≤ K_β T (ℓ + u + 2) e^{−λu/2} ‖X‖₁` (5.17), where
`K_β = C_d e^{2βJ_int}(1 + βJ_int)^6 log(2 + βJ_int)`.

**Formalization Note** `λ = c/(1 + βJ_int)` with universal `c ∈ (0, 1]`; `C_d > 0` depends only on
`dmax`; every interval `B`, every `ℓ ≥ |B|`, integer `u ≥ 0` and `T ≥ 0`. `w1` is `ℝ≥0∞`-valued. -/
theorem proposition_5_8 :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ dmax : ℕ, 2 ≤ dmax → ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i ∧ d i ≤ dmax) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ (ℓ : ℕ) (B : Finset (Fin N)), IsInterval B → B.card ≤ ℓ → ∀ u : ℕ, ∀ T : ℝ, 0 ≤ T →
            ∀ X : Op d, X.IsHermitian →
              w1 (blockChannel β (chain V W) B Finset.univ T X -
                  blockChannel β (chain V W) B (bdryNbhd B u) T X) ≤
                ENNReal.ofReal (Cd * Real.exp (2 * β * jint (chain V W)) *
                  (1 + β * jint (chain V W)) ^ 6 * Real.log (2 + β * jint (chain V W)) * T *
                  ((ℓ : ℝ) + u + 2) * Real.exp (-(c / (1 + β * jint (chain V W))) * u / 2) *
                  traceNorm X) := by sorry

end QDSGibbs
