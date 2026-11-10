-- Prove2me | Theorems.Thm_PRUMicrocrypt_lemma_3_1
-- name    : PRUMicrocrypt.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:37.014726+00:00
-- url     : https://prove2.me/theorems/d3dabf63-841d-4601-939c-586160903cbb
-- title:
--   Lemma 3.1 — recording restrictions for $V^L,V^R,V,W$ and their barred counterparts
-- statement:
--   Let $V^L,V^R,V,W$ be the recorders (3.3)–(3.8) and $\overline V^L,\overline V^R,\overline V,\overline W$ the barred recorders (3.9)–(3.14) on the query register $\otimes\,\mathcal H_{LR}$, $N=2^n$. For a partial isometry $Z$ write $\Pi_{D(Z)}=Z^\dagger Z$ and $\Pi_{I(Z)}=ZZ^\dagger$. Then:
--
--   1. each of $V^L,V^R,V,W,\overline V^L,\overline V^R,\overline V,\overline W$ is a partial isometry, and it and its adjoint increase the total record size $|L|+|R|$ by at most one;
--   2. $W^\dagger V=\Pi_{D(W)}$ and $WV^\dagger=\Pi_{I(W)}$;
--   3. $\overline W^\dagger\overline V=\Pi_{D(\overline W)}$ and $\overline W\,\overline V^\dagger=\Pi_{I(\overline W)}$;
--   4. $\Pi_{D(W)},\Pi_{I(W)},\Pi_{D(\overline W)},\Pi_{I(\overline W)}$ commute with the total record size;
--   5. $V,W,\overline V,\overline W$ and their adjoints are contractions.
--
--   These restriction identities let the analysis replace the unrestricted recorder by the bijective one on the domain of $W$ (H.1).
--
--   Differences from the source:
--   - encoding: operators on query ⊗ ℋ_LR → matrices in the orthonormal basis |x⟩|L, R⟩ of multiset records; reason: the kets (3.2) are an orthonormal basis, so no operator changes
--   - encoding: increase total record size by at most one; commute with total record size → nonzero entries only from size s to size ≤ s + 1; commuting with every projector Π_{size = s}; reason: the same properties written in the record basis
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 3.1, p.23 (definitions (3.2)–(3.14), pp.21–22)

import Mathlib
import Definitions.Def_PRUMicrocrypt_recorderHat

set_option autoImplicit false

namespace PRUMicrocrypt

open Matrix

/-- **Lemma 3.1 (Recording restrictions).** "The operators V^L, V^R, V, W and their barred
counterparts are partial isometries. They and their adjoints increase total record size by at most
one, and W†V = Π_{D(W)}, WV† = Π_{I(W)}. (3.15) The barred operators satisfy W̄†V̄ = Π_{D(W̄)},
W̄V̄† = Π_{I(W̄)}. (3.16) The projectors onto the domain and image of W and W̄ commute with total
record size. In particular, all four recorders and their adjoints are contractions."
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), Lemma 3.1, p.23 (definitions (3.2)–(3.14), pp.21–22).

**Formalization Note.** Operators on query ⊗ LR are matrices in the orthonormal basis `|x⟩|L, R⟩`
(`Record`). `Π_{D(Z)} = Z†Z`, `Π_{I(Z)} = ZZ†` (p.22). "Increase total record size by at most
one" is: a nonzero matrix entry `⟨y, L', R'|Z|x, L, R⟩` has `|L'| + |R'| ≤ |L| + |R| + 1`.
"Commute with total record size" is commuting with every projector `Π_{size = s}`. The four
recorders are `V, W, V̄, W̄`. -/
theorem lemma_3_1 (n : ℕ) :
    (∀ Z ∈ [VL n, VR n, Vrec n, Wrec n, VLbar n, VRbar n, Vbar n, Wbar n],
      IsPartialIsometry Z ∧ IncreasesSizeAtMostOne Z ∧ IncreasesSizeAtMostOne Zᴴ) ∧
    ((Wrec n)ᴴ * Vrec n = (Wrec n)ᴴ * Wrec n ∧ Wrec n * (Vrec n)ᴴ = Wrec n * (Wrec n)ᴴ) ∧
    ((Wbar n)ᴴ * Vbar n = (Wbar n)ᴴ * Wbar n ∧ Wbar n * (Vbar n)ᴴ = Wbar n * (Wbar n)ᴴ) ∧
    (∀ s : ℕ, Commute ((Wrec n)ᴴ * Wrec n) (sizeProj n s) ∧
      Commute (Wrec n * (Wrec n)ᴴ) (sizeProj n s) ∧
      Commute ((Wbar n)ᴴ * Wbar n) (sizeProj n s) ∧
      Commute (Wbar n * (Wbar n)ᴴ) (sizeProj n s)) ∧
    (∀ Z ∈ [Vrec n, Wrec n, Vbar n, Wbar n], IsContraction Z ∧ IsContraction Zᴴ) := by sorry

end PRUMicrocrypt
