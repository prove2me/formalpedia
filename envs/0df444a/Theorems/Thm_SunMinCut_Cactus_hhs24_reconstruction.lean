-- Prove2me | Theorems.Thm_SunMinCut_Cactus_hhs24_reconstruction
-- name    : SunMinCut.Cactus.hhs24_reconstruction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:25:35.472911+00:00
-- url     : https://prove2.me/theorems/b70b9b14-dc2f-487b-9cc5-e9572c3a5e7c
-- title:
--   App. G.3 — the He–Huang–Saranurak reconstruction in O(s α_UF(s, n) + nL)
-- statement:
--   There are one admissible deterministic program and one constant $C$ such that, for every connected aggregated graph $G$ ($m=s$ records) on $n\ge2$ vertices with positive capacities, every root $r$, every collection of $L$ original spanning trees $T_0,\dots,T_{L-1}$ (spanning trees contained in the support graph of $G$), and canonical labels by at most two tree edges, $(\text{type},x,y,j)$ denoting $T_{j,x}$ or $T_{j,x}\triangle T_{j,y}$, for every vertex's and every edge's minimal root-avoiding minimum cut, with the common absence label $V$ (and identical labels for identical shores), every execution on the encoded input halts within $C\,(s\,\alpha_{UF}(s,n)+nL)$ operations and outputs a cactus $(K,\pi)$ representing exactly all minimum cuts of $G$.
--
--   Differences from the source:
--   - encoding: "in O(·) operations the procedure …" (a statement about the paper's procedure) → there exist one admissible program P for the real RAM of footnote 1 and one constant C, chosen before every input, with the stated time bound on every draw tape; reason: the O(·) is unpacked with its constant fixed before the input, and the procedure is the program that realizes it
--   - generalization: a program for the unit-cost real RAM (machine constants unrestricted) → the program must be admissible: rational constants only; reason: a stronger claim; an admissible program is in particular a real-RAM program, so the Lean statement implies the source's
--   - encoding: input with s aggregated endpoint pairs and bound in s → Aggregated G (no loops, no repeated pair), so m = s, and the bound written with m; reason: the procedure takes the aggregated graph of §2 as input
--   - encoding: α_UF, "the inverse Ackermann function" → Tarjan's two-argument α(s, n) = min{i ≥ 1 : A(i, max(1, ⌊s/n⌋)) > log₂ n}; reason: the standard union-find convention; others differ by additive constants
--   - encoding: "original spanning trees" → spanning trees on V contained in the support graph of G; reason: the source trees are spanning forests of copies of G's edges
--   - encoding: deterministic work (Appendix B.1 or Appendix G) → Deterministic P forbids uniform-draw instructions, with the guarantee on every tape; reason: the run is independent of the tape; this states determinism directly
--   - encoding: the arithmetic, logarithm and power operations of footnote 1 → division by zero is zero, log uses log(abs x), and power returns zero on negative bases instead of using the cosine continuation of Real.rpow; reason: explicit totalization at exceptional inputs using constant-cost guards; the paper’s uses of real powers have nonnegative bases and no trigonometric operation is introduced
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, App. G.3, Reconstruction paragraph ([HHS24, Lemma 3.2 and Appendix A]), p. 50

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Graph
import Definitions.Def_SunMinCut_Cactus_CactusGraph
import Definitions.Def_SunMinCut_Cactus_Machine
import Definitions.Def_SunMinCut_Cactus_Intervals

namespace SunMinCut.Cactus

/-- **The reconstruction of He–Huang–Saranurak** ([HHS24, Lemma 3.2 and Appendix A]) in the form
stated by Sun 2026, doi:10.5281/zenodo.23915020, App. G.3, p. 50: given the aggregated weighted
graph (`m = s` records), a collection of `L` original spanning trees, and canonical labels by at
most two tree edges for every vertex's and every edge's minimal root-avoiding minimum cut, with
the common absence label, one program constructs a cactus representing exactly all minimum cuts
in `O(s α_UF(s, n) + nL)` time. -/
theorem hhs24_reconstruction :
    ∃ P : Program, Admissible P ∧ Deterministic P ∧ ∃ C : ℝ,
      ∀ (n m : ℕ), 2 ≤ n → ∀ G : Graph n m, Positive G → Connected G → Aggregated G →
      ∀ (r : Fin n) (L : ℕ) (T : Fin L → SimpleGraph (Fin n)),
        (∀ j, (T j).IsTree ∧ T j ≤ supportGraph G) →
      ∀ (lv : Fin n → Option TreeLabel) (le : Fin m → Option TreeLabel),
        CanonicalLabels G r T lv le →
      ∀ (lG : List ℝ) (lT : Fin L → List ℝ), GraphCode G lG → (∀ j, EdgeListCode (T j) (lT j)) →
        HaltsWithin P
          (lG ++ [((r : ℕ) : ℝ), (L : ℝ)] ++ (List.ofFn lT).flatten ++
            (List.ofFn fun v => labelCode (lv v)).flatten ++
            (List.ofFn fun x => labelCode (le x)).flatten)
          (C * ((m : ℝ) * alphaUF m n + (n : ℝ) * L)) ∧
        ∀ ω : Tape, ∃ (q e : ℕ) (K : MGraph q e) (π : Fin n → Fin q),
          CactusCode K π (outputAt P
            (lG ++ [((r : ℕ) : ℝ), (L : ℝ)] ++ (List.ofFn lT).flatten ++
              (List.ofFn fun v => labelCode (lv v)).flatten ++
              (List.ofFn fun x => labelCode (le x)).flatten)
            (C * ((m : ℝ) * alphaUF m n + (n : ℝ) * L)) ω) ∧
          RepresentsMinCuts G K π := by sorry

end SunMinCut.Cactus
