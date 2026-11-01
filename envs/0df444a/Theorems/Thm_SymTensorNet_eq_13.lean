-- Prove2me | Theorems.Thm_SymTensorNet_eq_13
-- name    : SymTensorNet.eq_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:25.920882+00:00
-- url     : https://prove2.me/theorems/1efabc40-15c0-4132-b5d5-9b7f89b88fef
-- title:
--   Eq. (13) — the two coupled bases are related by a unitary $F^{abc}_d$
-- statement:
--   Let $G$ be a group with fusion data for a catalogue of irreps, and let $a,b,c,d$ be charges. Let $Q^{abcd}_e$ ($e$ running over the labels of Eq. (11), fusing $a\otimes b$ first) and $\tilde Q^{abcd}_f$ ($f$ running over the labels of Eq. (12), fusing $b\otimes c$ first) be the changes of basis to the two coupled bases $|dp_d;e\rangle$ and $|dp_d;f\rangle$. Then there is a unitary matrix $F^{abc}_d$, with rows indexed by $e$ and columns by $f$, such that
--   $$\tilde Q^{abcd}_f=\sum_e(F^{abc}_d)^e_f\,Q^{abcd}_e$$
--   entrywise, for all $m_a,n_b,o_c,p_d$. The matrix depends only on $a,b,c,d$ and the fusion data, not on $p_d$; for $G=SU(2)$ its entries are the $6j$ symbols.
--
--   Differences from the source:
--   - generalization: a compact, completely reducible group G → any group G (no topology); reason: compactness only supplies complete reducibility, which unitarity gives; compact groups are an instance.
--   - generalization: G multiplicity free, F indexed by intermediate charges e, f → F indexed by pairs of channels; reason: footnote [10]; with multiplicity freeness the labels are the intermediate charges.
--   - encoding: the 6-index tensor (F^{abc}_d)^e_f → for each (a, b, c, d) a unitary matrix with rows e and columns f; reason: same numbers, arranged as a matrix.
-- source:
--   Singh, Pfeifer & Vidal, Tensor network decompositions in the presence of a global symmetry, arXiv:0907.2994v2, Eq. (13) and the sentence before it, p.3

import Mathlib
import Definitions.Def_SymTensorNet_FewLegs

namespace SymTensorNet

universe u v

open Matrix

/-- **Eq. (13): the two coupled bases are related by a unitary `F`.** For all charges `a, b, c, d`
there is a unitary matrix `F^{abc}_d` with rows the coupled-basis labels `e` of Eq. (11) and
columns the labels `f` of Eq. (12), depending only on `a, b, c, d` and the fusion data (not on the
basis index `p_d`), such that `Q̃^{abcd}_f = Σ_e (F^{abc}_d)^e_f Q^{abcd}_e` entrywise.

arXiv:0907.2994v2, p.3, Eq. (13) ("The two coupled bases are related by a unitary transformation
given by the 6-index tensor F").

**Formalization Note** Beyond multiplicity freeness the labels `e`, `f` are pairs of channels
(footnote [10]); `G` is a bare group. -/
theorem eq_13 {G : Type u} [Group G] (F : FusionData.{u, v} G) (a b c d : F.Charge) : ∃ Fm : Matrix (Lab11 F a b c d) (Lab12 F a b c d) ℂ, Fm * Fmᴴ = 1 ∧ Fmᴴ * Fm = 1 ∧ ∀ (f : Lab12 F a b c d) (m : Fin (F.dim a)) (n : Fin (F.dim b)) (o : Fin (F.dim c)) (p : Fin (F.dim d)), Q12 F f m n o p = ∑ e : Lab11 F a b c d, Fm e f * Q11 F e m n o p := by sorry

end SymTensorNet
