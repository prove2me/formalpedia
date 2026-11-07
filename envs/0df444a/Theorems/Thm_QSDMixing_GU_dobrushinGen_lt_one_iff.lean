-- Prove2me | Theorems.Thm_QSDMixing_GU_dobrushinGen_lt_one_iff
-- name    : QSDMixing.GU.dobrushinGen_lt_one_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:38.359932+00:00
-- url     : https://prove2.me/theorems/10d6fb07-bc5a-4bdd-9946-ac5757c075a2
-- title:
--   Proposition 15 — $\kappa_{\mathrm{gen}}(T)<1$ iff $\max_{g\notin H}|\langle\psi|U_g|\psi\rangle|<1$
-- statement:
--   For a geometrically uniform ensemble on $G/H$, with $T=\Phi_X|_{\mathcal A}$,
--
--   $$
--   \kappa_{\mathrm{gen}}(T)<1\iff\max_{g\notin H}|\langle\psi|U_g|\psi\rangle|<1.
--   $$
--
--   The condition says that distinct coset states are not perfectly overlapping. Both directions are stated.
--
--   **Formalization Note** At $G=H$ the maximum is undefined, the Lean condition holds vacuously, and $\kappa_{\mathrm{gen}}=0$, so both sides hold.
--
--   Differences from the source:
--   - encoding: max_{g∉H} |⟨ψ|U_g|ψ⟩| < 1 → for every g ∉ H, ‖⟨ψ, U_g ψ⟩‖ < 1; reason: G is finite, so these agree whenever the maximum is defined; at G = H the maximum is undefined and all quantities equal 1 or 0
--   - reading: "a Hilbert space ℋ", with no dimension → every ℓ²(ι), for an arbitrary type ι, with k-fold tensor power ℓ²(Fin k → ι); reason: every complex Hilbert space is unitarily ℓ²(ι), and the finite-dimensional reading would be the weaker one
--   - encoding: the channel T = Φ_X|_A on the algebra A → the map Φ_X on all of M_n(ℂ), with the suprema taken over D(A); reason: Φ_X preserves A, and only its values on D(A) enter
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.1, Proposition 15, p.18; proof pp.18–19

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_stabilizer
import Definitions.Def_QSDMixing_GU_cosetFintype
import Definitions.Def_QSDMixing_GU_gram
import Definitions.Def_QSDMixing_GU_hecke
import Definitions.Def_QSDMixing_GU_dobrushinGen
import Definitions.Def_QSDMixing_GU_schurChannel

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- **Proposition 15, p.18.** `κ_gen(T) < 1 ⟺ max_{g ∉ H} |⟨ψ| U_g |ψ⟩| < 1`, for `T = Φ_X|_A`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §3.1, Proposition 15, pp.18–19.

**Formalization Note.** `max_{g ∉ H} |…| < 1` is written `∀ g ∉ H, ‖⟨ψ, U_g ψ⟩‖ < 1`. `G` is finite, so the two agree whenever the
maximum is defined. At `G = H` the maximum is undefined and the Lean condition is vacuously true, and `κ_gen = 0`: both sides hold. -/
theorem dobrushinGen_lt_one_iff {G ι : Type} [Group G] [Finite G]
    (U : G →* unitary (Ell2 ι →L[ℂ] Ell2 ι)) (ψ : Ell2 ι) (hψ : ‖ψ‖ = 1) :
    dobrushinGen (hecke (stabilizer U ψ)) (schurChannel (gram U ψ)) < 1 ↔
      ∀ g ∉ stabilizer U ψ, ‖(inner ℂ ψ ((U g : Ell2 ι →L[ℂ] Ell2 ι) ψ) : ℂ)‖ < 1 := by sorry

end QSDMixing.GU
