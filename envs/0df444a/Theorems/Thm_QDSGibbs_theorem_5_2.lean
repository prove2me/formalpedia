-- Prove2me | Theorems.Thm_QDSGibbs_theorem_5_2
-- name    : QDSGibbs.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:08.762649+00:00
-- url     : https://prove2.me/theorems/77315626-a5ce-4350-95da-2b63b4fe36e9
-- title:
--   Theorem 5.2 — field-uniform stretched-exponential clustering on chains
-- statement:
--   There are universal constants $C_*,c_*>0$ such that for every nearest-neighbour chain (arbitrary on-site fields), every $0<\beta<\infty$, and observables $A,B$ supported on disjoint intervals at distance $R$,
--
--   $$
--   |\mathrm{Cov}_{\sigma_\beta}(A,B)|\le C_*\|A\|\,\|B\|\exp\Big[-c_*\frac{e^{-4\beta J_{\mathrm{int}}}}{1+\beta J_{\mathrm{int}}}\sqrt R\Big].
--   $$
--
--   The constants do not depend on $N$, the lengths of the supports, or the local dimensions. The same estimate, with the same constants, holds for the Gibbs state of the Hamiltonian restricted to any subinterval.
--
--   This is the covariance profile that feeds the boundary influence estimate (Lemmas 5.9 and 5.10).
--
--   **Formalization Note** For the restricted clause, $J_{\mathrm{int}}$ is that of the restricted Hamiltonian, which is at most the global one.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: observables "at distance $R$" → supports at distance at least $R$, $R\ge0$; reason: the bound decreases in $R$, so the two statements are equivalent
--   - reading: "the same estimate … for the Gibbs state of the Hamiltonian restricted to any subinterval" → the estimate with $J_{\mathrm{int}}(H_\Omega)$, the interaction strength of the restricted Hamiltonian; reason: applying the theorem to the restricted chain gives its own $J_{\mathrm{int}}$; since $J_{\mathrm{int}}(H_\Omega)\le J_{\mathrm{int}}(H)$ and the bound increases in $J_{\mathrm{int}}$, this is the stronger reading
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 5.2, p.40

import Mathlib
import Definitions.Def_QDSGibbs_chainGen
import Definitions.Def_QDSGibbs_cov

open scoped Matrix

namespace QDSGibbs

/-- **Theorem 5.2** (arXiv:2610.03578, held file sha256 ede55815…, Theorem 5.2, p.40). There are
universal constants `C_*, c_* > 0` such that, for every `0 < β < ∞` and observables `A, B` supported
on disjoint intervals at distance `R`,
`|Cov_{σ_β}(A, B)| ≤ C_* ‖A‖‖B‖ exp[−c_* (e^{−4βJ_int}/(1 + βJ_int)) √R]` (5.5). The constants do
not depend on `N`, the lengths of the supports, or the local dimensions. The same estimate, with the
same constants, holds for the Gibbs state of the Hamiltonian restricted to any subinterval.

**Formalization Note** `C_*, c_*` come before `N`, the local dimensions (`d_i ≥ 2`), `β` and the
chain terms (arbitrary on-site fields). "At distance `R`" is encoded as "at distance at least `R`"
(`DistGe`, `R ≥ 0`): the bound decreases in `R`, so this is equivalent. Observables are arbitrary
operators. For the restricted clause, the state is `gibbs β (hamOn I Ω)` = `σ^Ω_β ⊗ 1/dim` (same
covariances for observables inside `Ω`) and `J_int` is that of the restricted Hamiltonian,
`jintOn I Ω ≤ jint I`. -/
theorem theorem_5_2 :
    ∃ Cs cs : ℝ, 0 < Cs ∧ 0 < cs ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          (∀ SA SB : Finset (Fin N), IsInterval SA → IsInterval SB → Disjoint SA SB →
            ∀ R : ℝ, 0 ≤ R → DistGe SA SB R → ∀ A B : Op d, SupportedOn SA A → SupportedOn SB B →
              ‖cov (gibbs β (ham (chain V W))) A B‖ ≤
                Cs * opNorm A * opNorm B *
                  Real.exp (-(cs * (Real.exp (-(4 * β * jint (chain V W))) /
                    (1 + β * jint (chain V W))) * Real.sqrt R))) ∧
          (∀ Ω : Finset (Fin N), IsInterval Ω →
            ∀ SA SB : Finset (Fin N), IsInterval SA → IsInterval SB → SA ⊆ Ω → SB ⊆ Ω →
              Disjoint SA SB → ∀ R : ℝ, 0 ≤ R → DistGe SA SB R →
                ∀ A B : Op d, SupportedOn SA A → SupportedOn SB B →
                  ‖cov (gibbs β (hamOn (chain V W) Ω)) A B‖ ≤
                    Cs * opNorm A * opNorm B *
                      Real.exp (-(cs * (Real.exp (-(4 * β * jintOn (chain V W) Ω)) /
                        (1 + β * jintOn (chain V W) Ω)) * Real.sqrt R))) := by sorry

end QDSGibbs
