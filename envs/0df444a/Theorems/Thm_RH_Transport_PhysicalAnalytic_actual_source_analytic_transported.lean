-- Prove2me | Theorems.Thm_RH_Transport_PhysicalAnalytic_actual_source_analytic_transported
-- name    : RH.Transport.PhysicalAnalytic.actual_source_analytic_transported
-- status  : Proved
-- author  : @Himan
-- created : 2026-11-15T03:27:23.267706+00:00
-- url     : https://prove2.me/theorems/2086697c-287e-40bc-8c31-fd23ade15356
-- title:
--   The source correction is analytic and within $1/2$ of $1$ on $\operatorname{Re}s>\tfrac78-\tfrac p4$, for $p<1/1000$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are $p=214651/1250000000$, the Gram exponent $b=192821/1562500$, the total slot length $\ell=\tfrac16+p$, the row and column exponents $\ell_x=(1-\ell-b)/2$ and $\ell_y=(1-\ell+b)/2$, the conductor exponent $h=(1+3\ell+b)/2$, the cushion $\zeta=1/(8\cdot 10^{12})$, the boundary $B=\tfrac{11}{12}-\tfrac{\ell}{4}=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s+\ell_x/2-1+h/6=s-2147607/3125000$.
--
--   Let $p<1/1000$ be real and write $B(p)=\tfrac78-\tfrac p4$ for the transported boundary of the refinement's geometry at $p$ (so that $B(p)=B$ at the tuned value of $p$). Let $S$ be a finite set of prime ideals of $\mathcal O$ satisfying OpenAI's source exclusions (it contains the fixed bad primes and satisfies the correction tail bound), let $\eta$ be a Hecke character, let $\chi$ be $\eta$ with the primes of $S$ deleted, and let $H(s)$ be the source correction of $\eta$ for $S$. Then:
--
--   1. **Deletion.** For every ideal $I$ of $\mathcal O$, the ideal coefficient of $\chi$ at $I$ equals that of $\eta$ if $I$ is coprime to the modulus of $\chi$, and is $0$ otherwise.
--
--   2. **Analyticity.** $H$ is analytic on the half-plane $\{s:\operatorname{Re}s>B(p)\}$.
--
--   3. **Size.** For every $s$ with $\operatorname{Re}s>B(p)$,
--   $$
--   |H(s)-1|\le\frac12 .
--   $$
--
--   This is the analytic input on the correction factor in the common probe contract: the source's own correction and its own excluded-prime character already satisfy the requirements on the larger half-plane, with no enlargement of the exclusion set.
--
--   **Formalization Note** $B(p)$ is `RH.Transport.Geometry.boundary p`; $\chi$ is `η.excludePrimes S hS.prime`; $H$ is `PrincipalSignalComparison.sourceCorrection η S`; `SourceExclusions` is `OAI.SevenEighths.ProbePhysical.SourceExclusions`. Coprimality of ideals is decided classically.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalAnalytic/SourceCorrection.lean, theorem actual_source_analytic_transported (L91-L102): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalAnalytic/SourceCorrection.lean#L91-L102

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic ProbeEuler ProbePhysical HeckeFamily
open PrincipalSignalComparison
local notation "O" => ActualEisensteinCubic.O
noncomputable section

theorem RH.Transport.PhysicalAnalytic.actual_source_analytic_transported
    (p : ℝ) (hp : p < 1 / 1000) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) :
    (∀ I, idealCoeff (η.excludePrimes S hS.prime) I =
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S)
      {s : ℂ | Geometry.boundary p < s.re} ∧
    (∀ s : ℂ, Geometry.boundary p < s.re →
      ‖sourceCorrection η S s - 1‖ ≤ (1 / 2 : ℝ)) := by sorry
