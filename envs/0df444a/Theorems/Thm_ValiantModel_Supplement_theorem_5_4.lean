-- Prove2me | Theorems.Thm_ValiantModel_Supplement_theorem_5_4
-- name    : ValiantModel.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:24:42.341642+00:00
-- url     : https://prove2.me/theorems/c04e489d-3672-4dec-a86d-e57c604ac8da
-- title:
--   Theorem 5.4, p.36 — the conditions of Theorem 1.5 are not tight
-- statement:
--   In Valiant's model over a general domain (Definition 3):
--
--   1. (Finite VC dimension is not sufficient.) There exists a concept class $H$ with $\mathrm{VC}(H)<\infty$ that is not learnable.
--   2. (Finite 1-star number is not necessary.) There exists a concept class $H$ with $s_1(H)=\infty$ that is learnable.
--   3. (The whole-domain 1-star condition is not necessary.) There exists a concept class $H$ that is not learnable, even though the whole domain is not a 1-star for $H$.
--
--   Hence none of the three criteria of Theorem 1.5 characterizes learnability over arbitrary domains.
--
--   Differences from the source:
--   - generalization: there exist a domain and a class → there exist a countable domain with the discrete σ-algebra and a class; reason: more specific witnesses imply the source's statements; the paper's witnesses are ℤ, ℤ × {0,1} and ℕ
--   - encoding: every distribution D over X → every probability measure on X with the discrete σ-algebra (`DiscreteMeasurableSpace`), with compatibility almost surely and the error by the outer measure; reason: the paper fixes no σ-algebra; with all subsets measurable every concept and every output is an event
--   - encoding: a randomized learner → `RandProtocol`: an arbitrary probability space of internal randomness and a deterministic `GProtocol` for each value, success probability by the lower Lebesgue integral; reason: this is exact whenever the success event is measurable, and the paper's probability is defined only then; examples and queries interleave, queries may be asked anywhere, and outputs are improper
--   - encoding: learnable → `GLearnable`: some learner and some m with at most m(ε, δ) calls on each oracle; reason: Definition 3, budget per oracle
--   - encoding: VC(H) < ∞, s₁(H) = ∞ → `vcDim H < ⊤`, `oneStarNumber H = ⊤`; reason: ℕ∞-valued dimensions
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Theorem 5.4, p.36 (PDF p.38); proof pp.36–37 (PDF pp.38–39)

import Mathlib
import Definitions.Def_HighDimProb_Chaining_VcDim
import Definitions.Def_ValiantModel_Supplement_GeneralModel
import Definitions.Def_ValiantModel_Supplement_StarNumber

open HighDimProb.Chaining

namespace ValiantModel.Supplement

/-- **Theorem 5.4**, Hanneke, Mehrotra, Velegkas, Zampetakis, arXiv:2605.13840 (version held, sha256
f793f255…), p.36 (PDF p.38), in Valiant's model over a general domain (Definition 3):
1. (finite VC dimension is not sufficient) some `H` with `VC(H) < ∞` is not learnable;
2. (finite 1-star number is not necessary) some `H` with `s₁(H) = ∞` is learnable;
3. (the whole-domain 1-star condition is not necessary) some `H` is not learnable although the whole
   domain is not a 1-star for `H`.

**Formalization Note.** Each witness domain carries the discrete σ-algebra and is required to be
countable (the page's witnesses are `ℤ`, `ℤ × {0,1}` and `ℕ`); on a countable domain the probability
measures on all subsets are exactly the distributions (probability mass functions) of §3. -/
theorem theorem_5_4 :
    (∃ (X : Type) (_ : MeasurableSpace X), DiscreteMeasurableSpace X ∧ Countable X ∧
      ∃ H : Set (X → Bool), vcDim H < ⊤ ∧ ¬ GLearnable H) ∧
    (∃ (X : Type) (_ : MeasurableSpace X), DiscreteMeasurableSpace X ∧ Countable X ∧
      ∃ H : Set (X → Bool), oneStarNumber H = ⊤ ∧ GLearnable H) ∧
    (∃ (X : Type) (_ : MeasurableSpace X), DiscreteMeasurableSpace X ∧ Countable X ∧
      ∃ H : Set (X → Bool), ¬ IsStarSet H (fun _ => true) Set.univ ∧ ¬ GLearnable H) := by sorry

end ValiantModel.Supplement
