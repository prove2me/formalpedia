-- Prove2me | Theorems.Thm_PhyloCSP_lemma_9_2
-- name    : PhyloCSP.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:54.359149+00:00
-- url     : https://prove2.me/theorems/cde4accc-55fc-48a9-b4c0-eea9d4283287
-- title:
--   Lemma 9.2 — $\sim$ is an equivalence relation with convex interval classes
-- statement:
--   Let $<$ be a random linear order on $Z$ whose distribution is invariant under $\mathrm{Aut}(\mathcal F)$, and define $\sim$ by eq. (9): $x\sim y$ iff $x=y$ or $a<x\Leftrightarrow a<y$ for every $a$ with $a\mid_C xy$. Then almost surely:
--
--   1. $\sim$ is an equivalence relation;
--   2. each equivalence class is an interval with respect to $<$;
--   3. the restriction of $<$ to each equivalence class is $C$-convex: for distinct $a,b,c$ in one class, $a\mid_C bc$ implies that $a$ is not between $b$ and $c$.
--
--   The relation $\sim$ and the induced order $\prec$ on its classes are the first invariants extracted from a random invariant order.
--
--   Differences from the source:
--   - encoding: a random linear order < on Z with Aut(F)-invariant distribution → a measurable map Ω → (Z → Z → Bool) every realization of which is a strict total order, with the law of (g a <? g b)_{a,b} equal to that of (a <? b)_{a,b} for every g ∈ AutF; reason: invariance under all g is the same as invariance under all g⁻¹
--   - encoding: the Fraïssé limit F = (Z, C) and its automorphism group Aut(F) → the concrete structure (Z, fraisseRel) of Definition 7.5, Z = Finset ℚ, and AutF its automorphism group; reason: Theorem 7.4 and Appendix B.1 identify the concrete structure with F, which is unique up to isomorphism; the statement is invariant under isomorphism
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 9.2, pp.26–27 (PDF pp.28–29); eq. (9), p.26; (6), p.23

import Mathlib
import Definitions.Def_PhyloCSP_AutF
import Definitions.Def_PhyloCSP_RankRelations
import Definitions.Def_PhyloCSP_IsConvexOrder

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 9.2, pp.26–27 (PDF pp.28–29), in the setting
of Section 9.1, p.26: "Consider a random linear order < on Z whose distribution is invariant under
Aut(F)." With `∼` defined by (9). "Lemma 9.2. Almost surely, the following hold: • ∼ is an
equivalence relation; • each equivalence class is an interval w.r.t. the order <; • the
restriction of < to each equivalence class is C-convex." C-convex on a set `W` is (6), p.23:
"C(a; b, c) implies a is not between b and c for all distinct a, b, c ∈ W".

**Formalization Note.** The random order is a measurable map `lt : Ω → (Z → Z → Bool)` (product
σ-algebra) whose every realization is a strict total order; invariance is equality of the laws of
`(lt (g a) (g b))_{a,b}` and `(lt a b)_{a,b}` for every `g ∈ Aut(F)`. `C = fraisseRel`. -/
theorem lemma_9_2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lt : Ω → Z → Z → Bool) (hmeas : Measurable lt)
    (horder : ∀ ω, IsStrictTotalOrder Z (fun a b => lt ω a b = true))
    (hinv : ∀ g ∈ AutF, P.map (fun ω a b => lt ω (g a) (g b)) = P.map lt) :
    ∀ᵐ ω ∂P,
      Equivalence (simRel (lt ω)) ∧
      (∀ x y z : Z, simRel (lt ω) x y → lt ω x z = true → lt ω z y = true →
        simRel (lt ω) x z) ∧
      (∀ a b c : Z, a ≠ b → a ≠ c → b ≠ c → simRel (lt ω) a b → simRel (lt ω) a c →
        fraisseRel a b c = true → ¬ Between (fun u v => lt ω u v = true) a b c) := by sorry

end PhyloCSP
