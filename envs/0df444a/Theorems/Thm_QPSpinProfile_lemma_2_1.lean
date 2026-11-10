-- Prove2me | Theorems.Thm_QPSpinProfile_lemma_2_1
-- name    : QPSpinProfile.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:01.82645+00:00
-- url     : https://prove2.me/theorems/99ed46a4-5611-41e1-90e2-99d73bd664af
-- title:
--   Lemma 2.1: the Pauli measurement satisfies (9) with $\kappa=4$
-- statement:
--   Let $\mathcal M_{\mathrm{Pauli}}$ be the measurement map of the Pauli POVM $E_{a,s}=\tfrac16(I+sa)$, $a\in\{X,Y,Z\}$, $s=\pm1$. Then for every finite-dimensional system $R$ and every Hermitian operator $\xi$ on $R\otimes\mathbb C^2$,
--   $$
--   \|\xi\|_1\le4\,\|(\mathrm{Id}_R\otimes\mathcal M_{\mathrm{Pauli}})(\xi)\|_1 ,
--   $$
--   i.e. the Pauli measurement satisfies the trace-norm comparison (9) with $\kappa_{\mathcal M}=4$.
--
--   This is the constant that enters the conditioning bound of Lemma 2.2 and hence Corollary 2.4.
--
--   Differences from the source:
--   - encoding: outcomes $(a,s)\in\{X,Y,Z\}\times\{\pm1\}$ and the map (10) → outcomes $k\in\mathrm{Fin}\,6$ and the published `measB` with orthonormal labels; reason: bijection of outcome sets; `measB` is the map $\mathrm{Id}_R\otimes\mathcal M$
--   - encoding: every finite-dimensional system $R$ → every finite type $R$ indexing a basis of $R$; reason: same quantifier
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Lemma 2.1, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_QPSpinProfile_pauliPOVM
import Definitions.Def_QPSpinProfile_SatisfiesDistortion

namespace QPSpinProfile

/-- **Lemma 2.1 (Trace-norm comparison for the Pauli measurement)** (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity in quantum spin glasses*, arXiv:2610.02166 (held version, sha256 a0a1ec89…), p.16, PDF p.19).
The measurement `M_Pauli` satisfies (9) with `κ_M = 4`: for every finite-dimensional system `R`
and every Hermitian `ξ` on `R ⊗ ℂ²`, `‖ξ‖₁ ≤ 4 ‖(Id_R ⊗ M_Pauli)(ξ)‖₁`. -/
theorem lemma_2_1 : SatisfiesDistortion pauliPOVM 4 := by sorry

end QPSpinProfile
