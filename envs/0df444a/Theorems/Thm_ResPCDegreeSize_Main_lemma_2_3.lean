-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_2_3
-- name    : ResPCDegreeSize.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:25:07.150926+00:00
-- url     : https://prove2.me/theorems/579aeb9f-f464-43ec-bc2a-c89640087bc0
-- title:
--   Lemma 2.3 — base change of $\mathcal C_D$
-- statement:
--   Let $Q\supseteq\mathrm{Bool}$, fix $D$, let $\mathcal C_D=\mathcal C_D(Q)$, and let $E/\mathbb F_p$ be a field extension. Regard $\mathcal C_D^E:=E\otimes_{\mathbb F_p}\mathcal C_D$ as an $E$-subspace of $E[x]_{\le D}$. For every $k\le D$,
--   $$E\otimes_{\mathbb F_p}(\mathcal C_D\cap V_k)=\mathcal C_D^E\cap E[x]_{\le k}.$$
--   Moreover, if $f\in\mathcal C_D^E$, $g\in E[x]$ and $\deg f+\deg g\le D$, then $fg\in\mathcal C_D^E$.
--
--   This transports the degree-bounded absorption of Fact 2.1 to coefficients in $\mathbb F_p(\lambda)$.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: E ⊗ W regarded inside E[x] under the natural identification → the E-span of the image of W under the coefficient map; reason: the natural map E ⊗ W → E[x] is injective for a field extension, and its image is that span
--   - encoding: E/F_p a field extension → a field E with an Algebra (ZMod p) E instance; reason: that instance is exactly a field extension of F_p
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 2.3, PDF p. 4 (printed p. 3)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_2_3 {n p : ℕ} [Fact p.Prime] (Q : Set (Poly n p)) (hQ : boolAxioms n p ⊆ Q)
    (D : ℕ) (E : Type*) [Field E] [Algebra (ZMod p) E] :
    (∀ k : ℕ, k ≤ D →
      extendScalars E (CD Q D ⊓ V n p k) =
        extendScalars E (CD Q D) ⊓ MvPolynomial.restrictTotalDegree (Fin n) E k) ∧
    (∀ f g : MvPolynomial (Fin n) E, f ∈ extendScalars E (CD Q D) →
      f.totalDegree + g.totalDegree ≤ D → f * g ∈ extendScalars E (CD Q D)) := by sorry

end ResPCDegreeSize.Main
