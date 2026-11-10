-- Prove2me | Theorems.Thm_TwMSOCount_Main_proposition_5_1
-- name    : TwMSOCount.Main.proposition_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:48:42.056656+00:00
-- url     : https://prove2.me/theorems/ef970c6c-abb4-406e-b86e-7b194099b1ee
-- title:
--   Proposition 5.1 — effective construction of the state map from $\theta$
-- statement:
--   Let $\theta = (k, C, \psi)$ with $C=\{0,\dots,r-1\}$, $r\ge1$. The graphs used by the recurrences are the well-formed graphs of treewidth at most $k$ with at most $6(k+1)$ boundary labels, the graphs on at most $6(k+1)$ boundary vertices alone, and the collections and candidate parents built from them.
--
--   **Proposition.** From $\theta$ one can compute a state map satisfying Definition 4.1, in the following sense: there is a state map $\mathrm{SM}_\theta$ for every $\theta$ and there are computable functions of $\theta$ that give, for every graph used by the recurrences, its state (from a code of the graph), a finite list of states for its label set containing it, the results of gluing, AddEdge and forgetting on these states (and whether they are defined), the values of the tests ($\mathrm{Width}_k$, $\mathrm{NoEdge}_Q$, $\mathrm{Piece}_Q$, $\Phi_{B,B_S,N}$, $\psi$, boundary colors and adjacency) on these states, and one finite representative graph (as a code) of each such state, with the same label set and state. The number of states, the representative sizes and the preprocessing time have computable bounds depending only on $\theta$.
--
--   **Formalization Note.** $\theta$ is passed as $(k, r, \mathrm{code}(\psi))$. The bounds on the number of states, on representative sizes and on preprocessing time follow from the computability of the listed functions: the state lists and representatives are computed from $\theta$, and only finitely many $\theta$ have a given size.
--
--   Differences from the source:
--   - encoding: a state map (Definition 4.1); the test Φ_{B,B_S,N} → StateMap with IsStateMap ψ (states coded by ℕ, finite sets T_B); Φ_{B,B_S,N} by its meaning PhiT from Appendix C.2; reason: Appendix C.2 gives the truth of Φ on every structure as First_{B,P} ∧ Sel_{B,P,N}; the computability of the bounds on |T_B| is meaningful only uniformly in θ and is the content of Proposition 5.1
--   - encoding: one can compute (the states, operation results, test values, representatives) → Computable functions stc, statesc, gluec, addc, forgetc, testc, repc of the code of θ, agreeing with a state map SMf θ on every used graph; reason: Mathlib computability on codes of graphs, label sets and tests
--   - encoding: the number of states, representative sizes and preprocessing time have computable bounds depending only on θ → implied by the computability of statesc and repc (a computable total function has a computable running time); reason: the bound is computed from θ by running these functions; finitely many θ have a given size
--   - encoding: results of operations and one finite representative graph for each state → operation results are the actual SMf states; each decoded representative has an injective boundary map and its actual SMf state equals the represented state; reason: a raw code with coincident boundary vertices or an unrelated stc value is not a representative of a boundaried-graph state
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), Proposition 5.1, p. 11 (PDF 12); proof in Appendix C.6, pp. 30–31 (PDF 31–32)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2
import Definitions.Def_TwMSOCount_Main_Weights
import Definitions.Def_TwMSOCount_Main_BGraph
import Definitions.Def_TwMSOCount_Main_Separator
import Definitions.Def_TwMSOCount_Main_Tables
import Definitions.Def_TwMSOCount_Main_Types

open Classical

namespace TwMSOCount.Main

theorem proposition_5_1 :
    ∃ (stc : (ℕ × ℕ × List ℕ) × GCode → ℕ)
      (statesc : (ℕ × ℕ × List ℕ) × List ℕ → List ℕ)
      (gluec : (ℕ × ℕ × List ℕ) × (List ℕ × ℕ) × (List ℕ × ℕ) → Option ℕ)
      (addc : (ℕ × ℕ × List ℕ) × List ℕ × (ℕ × ℕ) × ℕ → Option ℕ)
      (forgetc : (ℕ × ℕ × List ℕ) × List ℕ × ℕ × ℕ → Option ℕ)
      (testc : (ℕ × ℕ × List ℕ) × (ℕ × List ℕ × List ℕ × List ℕ) × ℕ → Bool)
      (repc : (ℕ × ℕ × List ℕ) × List ℕ × ℕ → GCode)
      (SMf : ∀ (k r : ℕ), Formula r Empty → StateMap r k),
      Computable stc ∧ Computable statesc ∧ Computable gluec ∧ Computable addc ∧
      Computable forgetc ∧ Computable testc ∧ Computable repc ∧
      ∀ (k r : ℕ) [NeZero r] (ψ : Formula r Empty), ψ.IsSentence →
        let θ : ℕ × ℕ × List ℕ := (k, r, ψ.encode (fun e => e.elim))
        (SMf k r ψ).IsStateMap ψ ∧
        (∀ H : BGraph r k, UsedGraph H →
          (SMf k r ψ).st H = stc (θ, encodeG H) ∧
          stc (θ, encodeG H) ∈ statesc (θ, labCode H.B)) ∧
        (∀ H₁ H₂ : BGraph r k, UsedGraph H₁ → UsedGraph H₂ →
          gluec (θ, (labCode H₁.B, stc (θ, encodeG H₁)), (labCode H₂.B, stc (θ, encodeG H₂))) =
            if BGraph.GlueOK H₁ H₂ then some ((SMf k r ψ).st (BGraph.glue H₁ H₂)) else none) ∧
        (∀ (H : BGraph r k) (a b : Lab k), UsedGraph H →
          addc (θ, labCode H.B, (a.val, b.val), stc (θ, encodeG H)) =
            if H.AddEdgeOK a b then some ((SMf k r ψ).st (H.addEdges {s(a, b)})) else none) ∧
        (∀ (H : BGraph r k) (b : Lab k), UsedGraph H →
          forgetc (θ, labCode H.B, b.val, stc (θ, encodeG H)) =
            if b ∈ H.B then some ((SMf k r ψ).st (H.forget b)) else none) ∧
        (∀ (H : BGraph r k) (t : ℕ × List ℕ × List ℕ × List ℕ), UsedGraph H →
          (testc (θ, t, stc (θ, encodeG H)) = true ↔ testSem ψ t H)) ∧
        (∀ H : BGraph r k, UsedGraph H →
          let R := decodeG r k (repc (θ, labCode H.B, stc (θ, encodeG H)))
          R.BoundaryWF ∧ R.B = H.B ∧
          (SMf k r ψ).st R = (SMf k r ψ).st H ∧
          stc (θ, encodeG R) = (SMf k r ψ).st R) := by sorry

end TwMSOCount.Main
