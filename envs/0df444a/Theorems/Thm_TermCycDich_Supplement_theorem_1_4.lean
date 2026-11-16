-- Prove2me | Theorems.Thm_TermCycDich_Supplement_theorem_1_4
-- name    : TermCycDich.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:49:50.989732+00:00
-- url     : https://prove2.me/theorems/bf48917e-94a6-4f75-afa9-83226d308b38
-- title:
--   Theorem 1.4 — Terminal Cyclability in $O(1783^k\cdot|G|)$ time on graphs of treewidth $\le k$, and in $O(36^k\cdot k\cdot|G|)$ time given a width-$k$ tree-decomposition
-- statement:
--   Let $k\ge1$. There is a deterministic algorithm that, given an annotated graph $(G,R)$ with $\mathrm{tw}(G)\le k$, decides whether $G$ has an $R$-cycle (a simple cycle through all red vertices) in time
--
--   $$O\big(1783^k\cdot|G|\big).$$
--
--   Moreover, if a tree-decomposition of $G$ of width at most $k$ is part of the input, the algorithm runs in time $O(36^k\cdot k\cdot|G|)$.
--
--   Precisely: there are a program and constants $C$, $\mathit{width}$ such that for every $k\ge1$ and every annotated graph with $\mathrm{tw}(G)\le k$ given by adjacency lists, the program halts with the correct verdict after at most $C\cdot1783^k\cdot\max(|G|,1)$ steps, all registers having at most $\mathit{width}\cdot(1+\log_2(2+1783^k(n+m+1)))$ bits; and likewise (with another program) within $C\cdot36^k\cdot k\cdot\max(|G|,1)$ steps when a tree-decomposition of width at most $k$ with at most $c\cdot k\cdot\max(|G|,1)$ bags is appended to the input, for every constant $c$ (the constants $C$, $\mathit{width}$ may depend on $c$, the program may not).
--
--   This single-exponential dynamic program is the last step of the polynomial-time algorithm of Theorem 1.1: applied to the logarithmic-width decompositions supplied by Theorem 1.2 it runs in $|G|^{2^{\mathrm{poly}(b)}}$ time.
--
--   **Formalization Note** The machine is the published deterministic word RAM `MinDegST.AddOne` (integer RAM `CongruencyTU`, unit cost, no coins, no oracle; time is the cost counter at halting). The constant $C$ is independent of $k$, and one program serves every $k$.
--
--   Differences from the source:
--   - reading: "there exists an algorithm" (no machine model named) → one deterministic program of the published word RAM MinDegST.AddOne (CongruencyTU integer RAM, unit cost per instruction, no coins, no oracle); time = cost counter at halting; reason: the paper fixes no model; a running time linear in |G| needs a RAM (on the base mission's Turing-machine adjacency-matrix encoding it is false)
--   - reading: word size unstated → every register has at most width·(1 + log₂(2 + T₀)) bits, T₀ = 1783^k·(n + m + 1) (resp. 36^k·k·(n + m + 1)), width fixed with the program; reason: words of O(log T) bits for the running time T, the standard convention for exponential-space dynamic programs; with O(log(n + m))-bit words a program can address only polynomially many cells
--   - reading: Let k ≥ 1 … there exists an algorithm … in time O(1783^k·|G|) (resp. O(36^k·k·|G|)) → one program and one constant C for all k ≥ 1, bound C·1783^k·max(|G|, 1) (resp. C·36^k·k·max(|G|, 1)); reason: the algorithm does not receive k (the proof guesses widths with Korhonen's algorithm); an O-constant depending on k would empty the exponential base; max(|G|, 1) only avoids a zero bound on the empty graph
--   - encoding: input annotated graph (G, R); output: solves Terminal Cyclability → adjacency lists (MinDegST.AddOne.encAdj with m = |E(G)|) followed by |R| and a duplicate-free list of R; output [1] if HasRCycle G R, [0] otherwise; reason: the paper names no input format
--   - reading: a tree-decomposition of width at most k is supplied as part of the input → a tree on Fin nb given by an edge list (each edge once), bags as duplicate-free lists of size ≤ k + 1, and nb ≤ c·k·max(|G|, 1) bags for an arbitrary constant c (width and the O-constant may depend on c, the program may not); reason: a bound O(36^k·k·|G|) cannot read a decomposition with more than O(k|G|) bags, so the paper's 'supplied decomposition' is one of linear size; the proof's own nice decomposition has O(k|G|) nodes, and every linear-size decomposition (in particular every nice one) is admitted
--   - encoding: tw(G) ≤ k → the public RobertsonSeymour1986.GM5.TreewidthLE G k; reason: same notion
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Theorem 1.4, p.14 (PDF 16), restated p.63 (PDF 65); proof pp.63–64 (PDF 65–66)

import Mathlib
import Definitions.Def_TermCycDich_HasRCycle
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_TermCycDich_Supplement_Input

namespace TermCycDich

namespace Supplement

/-- **Theorem 1.4** (single-exponential algorithm for Terminal Cyclability in the treewidth).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), Theorem 1.4, p.14 (PDF 16), restated p.63 (PDF 65): "Let k ≥ 1
be an integer. There exists an algorithm that takes as input an annotated graph (G, R) where
tw(G) ≤ k and solves Terminal Cyclability in time O(1783^k · |G|). Moreover, if a
tree-decomposition of width at most k for G is supplied as part of the input, the algorithm runs in
time O(36^k · k · |G|)."

**Formalization Note**
* Machine: the published deterministic word RAM `MinDegST.AddOne` (a `CongruencyTU.Program`
  without coins or oracle; time is the cost counter at halting). The graph is given by adjacency
  lists (`MinDegST.AddOne.encAdj`, with `m = |E(G)|`), followed by the list of red vertices
  (`tcInput`); "solves" is: the output is `[1]` if `G` has an `R`-cycle and `[0]` otherwise.
* Words: every register has at most `width · (1 + log₂(2 + T₀))` bits, with `T₀ = 1783^k·(n+m+1)`
  (resp. `36^k·k·(n+m+1)`), i.e. `O(log T)` bits for the running time `T`: enough to address the
  memory the algorithm can touch, and the usual convention for exponential-space dynamic programs;
  with `O(log(n+m))`-bit words a program could address only polynomially many cells.
* One program and one constant `C` serve every `k` (the algorithm does not receive `k`); `O(·)` is
  read as `C · 1783^k · max(|G|, 1)` (resp. `C · 36^k · k · max(|G|, 1)`), with `C` independent of
  `k`.
* Second claim: the supplied tree-decomposition has a tree on `Fin nb` given by an edge list
  (each edge once), bags given as duplicate-free lists of size at most `k + 1`, and at most
  `c · k · max(|G|, 1)` bags for an arbitrary constant `c` (the word size and the `O`-constant may
  depend on `c`, the program may not): a bound linear in `|G|` cannot read a decomposition with
  more than `O(k·|G|)` bags, and the proof itself works with a nice decomposition of `O(k|G|)`
  nodes, so every decomposition of linear size (in particular every nice one) is admitted.
* `tw(G) ≤ k` is the public `RobertsonSeymour1986.GM5.TreewidthLE G k`. -/
theorem theorem_1_4 :
    (∃ P : CongruencyTU.Program, MinDegST.AddOne.Deterministic P ∧ ∃ width C : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (R : Finset (Fin n))
        (adj : Fin n → List (Fin n)) (rl : List (Fin n)),
        MinDegST.AddOne.IsAdjListsOf G adj → rl.Nodup → rl.toFinset = R →
        RobertsonSeymour1986.GM5.TreewidthLE G k →
        MinDegST.AddOne.WordBounded P (tcInput n (MinDegST.AddOne.numEdges G) adj rl) width
            (1783 ^ k * (n + MinDegST.AddOne.numEdges G + 1)) ∧
          MinDegST.AddOne.HaltsWithin P (tcInput n (MinDegST.AddOne.numEdges G) adj rl)
            ((C : ℝ) * 1783 ^ k * (max n 1 : ℕ))
            (fun out => out = verdict (HasRCycle G (R : Set (Fin n))))) ∧
    (∃ P : CongruencyTU.Program, MinDegST.AddOne.Deterministic P ∧ ∀ c : ℕ, ∃ width C : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (R : Finset (Fin n))
        (adj : Fin n → List (Fin n)) (rl : List (Fin n)),
        MinDegST.AddOne.IsAdjListsOf G adj → rl.Nodup → rl.toFinset = R →
        ∀ (nb : ℕ) (bags : Fin nb → List (Fin n)) (te : List (Fin nb × Fin nb)),
          nb ≤ c * k * max n 1 → (∀ i, (bags i).Nodup ∧ (bags i).length ≤ k + 1) →
          MinDegST.AddOne.IsEdgeListOf (treeOfEdges te) te →
          RobertsonSeymour1986.GM5.IsTreeDecomposition G (treeOfEdges te)
            (fun i => (bags i).toFinset) →
          MinDegST.AddOne.WordBounded P
              (tdInput n (MinDegST.AddOne.numEdges G) adj rl nb bags te) width
              (36 ^ k * k * (n + MinDegST.AddOne.numEdges G + 1)) ∧
            MinDegST.AddOne.HaltsWithin P
              (tdInput n (MinDegST.AddOne.numEdges G) adj rl nb bags te)
              ((C : ℝ) * 36 ^ k * k * (max n 1 : ℕ))
              (fun out => out = verdict (HasRCycle G (R : Set (Fin n))))) := by sorry

end Supplement

end TermCycDich
