-- Prove2me | Theorems.Thm_TreeMultiflow_lemma_5_1_polytime
-- name    : TreeMultiflow.lemma_5_1_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:58.844697+00:00
-- url     : https://prove2.me/theorems/0c0bb2e4-28f0-43a2-8469-e86db561934f
-- title:
--   Lemma 5.1, polynomial-time part: the colouring of the local paths is computable in polynomial time
-- statement:
--   There is an algorithm, running in time polynomial in the binary length of an encoded star instance, that on every instance satisfying the hypotheses of Lemma 5.1 (bins of at most six paths, crossing colours from ten colours distinct within each bin, and case (a) or case (b)) outputs a colouring of the local paths with the ten colours, leaving the crossing colours unchanged, in which the paths of every bin receive distinct colours.
--
--   This is the clause "We can do this in polynomial time" of Lemma 5.1 (p.9); Appendix B (p.12) explains the construction. It is used for the polynomial-time claim of Theorem 1.2. The existence part is `TreeMultiflow.lemma_5_1`.
--
--   **Formalization Note** The algorithm is a function on encoded star instances (bins named by natural numbers, crossing colours below ten) computed by a Mathlib `TM2` Turing machine in polynomial time; it outputs the list of colours of the local paths.
--
--   Differences from the source:
--   - reading: we can do this in polynomial time → ∃ alg with Nonempty (Turing.TM2ComputableInPolyTime encStarInstance id alg), correct on every encoded instance satisfying the hypotheses of lemma_5_1; reason: the standard Turing-machine reading with binary numbers
--   - generalization: the bins at the leaves of an attached star → an abstract encoded bin instance (bins named by natural numbers), with the same predicates IsStarBinInstance and IsBinColouringExtension as lemma_5_1; reason: every attached star yields such an instance
--   - encoding: crossing colours from a set of ten colours, and the colouring of the local paths as the output → crossing colours as natural numbers with the hypothesis q.2 < 10, read through Fin.ofNat 10; output alg S : List (Fin 10), local path l gets (alg S).getD l 0, so a missing entry reads as colour 0; reason: the colours are unnamed, and the hypothesis excludes only numbers that are not colours; same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, p.9 (We can do this in polynomial time); Appendix B, p.12 (Running time)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_TreeMultiflow_IsStarBinInstance
import Definitions.Def_TreeMultiflow_IsBinColouringExtension
import Definitions.Def_TreeMultiflow_StarInstance
import Definitions.Def_TreeMultiflow_encStarInstance

namespace TreeMultiflow

/-- **Lemma 5.1, polynomial time.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
p.9: "The resulting coloring gives distinct colors to the paths in each bin. We can do this in
polynomial time." (Appendix B, p.12, "Running time", explains the construction.)

There is a map `alg` from encoded star instances to lists of colours, computable by a Turing
machine in time polynomial in the length of `encStarInstance`, such that on every instance whose
crossing colours are below ten and which satisfies the hypotheses of `lemma_5_1` (in case (a) or
case (b)), colouring local path `l` with the `l`-th entry of `alg S` satisfies the conclusion of
`lemma_5_1`.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` with input encoding
`encStarInstance` (alphabet `OnlineCRS.Combine.Sym`, binary numbers) and output the colour list
itself (alphabet `Fin 10`). The decoded instance has bins `ℕ`, local paths
`Fin S.locals.length`, crossing paths `Fin S.crossing.length`; the predicates are the same
`IsStarBinInstance` and `IsBinColouringExtension` as in `lemma_5_1`. A missing entry of the output
reads as colour `0`. -/
theorem lemma_5_1_polytime :
    ∃ alg : StarInstance → List (Fin 10),
      Nonempty (Turing.TM2ComputableInPolyTime encStarInstance (fun cs : List (Fin 10) => cs)
        alg) ∧
      ∀ S : StarInstance, (∀ q ∈ S.crossing, q.2 < 10) →
        IsStarBinInstance (fun l : Fin S.locals.length => (S.locals.get l).1)
          (fun l => (S.locals.get l).2) (fun c : Fin S.crossing.length => (S.crossing.get c).1)
          (fun c => Fin.ofNat 10 (S.crossing.get c).2) →
        ((∀ β : ℕ,
            (Finset.univ.filter fun c : Fin S.crossing.length => (S.crossing.get c).1 = β).card
              ≤ 4) ∨
          (Fintype.card (Fin S.crossing.length) ≤ 6 ∧
            Function.Injective (fun c : Fin S.crossing.length => Fin.ofNat 10 (S.crossing.get c).2))) →
        IsBinColouringExtension (fun l : Fin S.locals.length => (S.locals.get l).1)
          (fun l => (S.locals.get l).2) (fun c : Fin S.crossing.length => (S.crossing.get c).1)
          (fun c => Fin.ofNat 10 (S.crossing.get c).2) (fun l => (alg S).getD l 0) := by sorry

end TreeMultiflow
