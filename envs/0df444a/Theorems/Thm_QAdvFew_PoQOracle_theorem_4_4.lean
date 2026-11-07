-- Prove2me | Theorems.Thm_QAdvFew_PoQOracle_theorem_4_4
-- name    : QAdvFew.PoQOracle.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:24.653235+00:00
-- url     : https://prove2.me/theorems/c2a84f40-1570-4d7e-aa25-fa9fe89a52c1
-- title:
--   Theorem 4.4 — $\mathsf{PSPACE}^{\tilde f}\subseteq\mathsf{IP}^{\tilde f}$ for affine oracles
-- statement:
--   Let $f_n:\{0,1\}^n\to\{0,1\}$ be any family of functions and let $\tilde f=\{\mathrm{ML}_{2^d}[f_n]\}_{d,n\in\mathbb N}$ be the collection of its multilinear extensions over $\mathbb F_{2^d}$, with field elements represented by bit strings. Then
--   $$\mathsf{PSPACE}^{\tilde f}\subseteq\mathsf{IP}^{\tilde f}.$$
--
--   This is Corollary 34 of [AB17]: the arithmetization proof of $\mathsf{IP}=\mathsf{PSPACE}$ relativizes to oracles of this form.
--
--   Differences from the source:
--   - encoding: field elements represented by bit strings → the representation fixed by qPoly; a field-valued answer is given one bit per query; reason: the paper does not fix a representation
--   - reading: Each extension has total degree at most n → a property of the defined oracle, not stated in the conclusion; reason: it is an elementary remark about f̃ (§3.2.5), not a hypothesis or a claim of the inclusion
--   - encoding: classical oracles, Turing machines, the universal gate set → `Oracle = Str → Bool`, the finite-table machines `OTM`, Clifford+T with an XOR oracle gate; reason: an explicit model of the paper's §3.2 conventions; same classes
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Theorem 4.4, p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_affineOracle
import Definitions.Def_QAdvFew_PoQOracle_PSPACE
import Definitions.Def_QAdvFew_PoQOracle_IP

namespace QAdvFew.PoQOracle

/-- **Theorem 4.4 (Corollary 34 of [AB17])** (Goldin, Lombardi, Morimae, *Quantum Advantage has
Few Complexity Implications*, arXiv:2611.05303v1, Theorem 4.4, p. 23 (PDF p. 25)). Let
`{f_n : {0,1}^n → {0,1}}` be any family of functions and `f̃ = {ML_{2^d}[f_n]}_{d,n}` the collection
of its multilinear extensions over `F_{2^d}`, with field elements represented by bit strings. Then
`PSPACE^{f̃} ⊆ IP^{f̃}`.

**Formalization Note** `f̃` is `affineOracle f`, with the representation of `F_{2^d}` fixed by
`qPoly`. The sentence "Each extension has total degree at most `n`" is a property of `f̃`, not a
hypothesis. -/
theorem theorem_4_4 (f : (n : ℕ) → (Fin n → Bool) → Bool) :
    PSPACE (affineOracle f) ⊆ IP (affineOracle f) := by sorry

end QAdvFew.PoQOracle
