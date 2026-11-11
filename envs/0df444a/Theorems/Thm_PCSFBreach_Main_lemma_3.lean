-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_3
-- name    : PCSFBreach.Main.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:58.652677+00:00
-- url     : https://prove2.me/theorems/328e6d2e-6235-4996-96f5-ceaf5f78d7ca
-- title:
--   Lemma 3 — cost(alg1) ≤ 2·cost(F*) + q − 2·sl
-- statement:
--   Run the primal-dual algorithm with $\lambda=1$, $\mu=0$ on a PCSF instance, let $F'$ be the final grown forest, $H$ the moats, $Q$ the forced pairs, $D'=D\setminus Q$, and let $a$ be a balanced coloring. Let $\mathrm{alg}_1$ be an inclusion-wise minimal subforest of $F'$ connecting every pair of $D'$, and let $F^*$ be a forest. With $q$ and $sl$ the quantities of §3 defined from $a$ and $F^*$,
--   $$\mathrm{cost}(\mathrm{alg}_1)\le 2\cdot\mathrm{cost}(F^*)+q-2\cdot sl ,$$
--   costs taken with respect to the original pair set $D$.
--
--   This is the first of the three candidate bounds whose weighted average proves Theorem 1.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - generalization: the balanced coloring fixed with Lemma 1(iv) → every balanced coloring a of the run (IsBalanced); reason: the proof uses only feasibility and the balanced property; the computed coloring is one balanced coloring
--   - generalization: F* an optimal solution → F* any forest of the instance; reason: the proof never uses optimality of F*; an optimal forest is a forest
--   - encoding: Q = {i ∈ D : r_i = 1} (Algorithm 1, line 2) → Q = the forced pairs of the run (§2.1, p. 6); reason: the two sets coincide for a balanced coloring by Lemma 1(iv); §3's analysis (p. 8) takes Q from the primal-dual run
--   - encoding: r_i = l_i/(λπ_i) → r_i = l_i/(λπ_i) when π_i > 0, and r_i := 1 when π_i = 0; reason: the paper removes pairs with π_i = 0 without loss of generality (p. 4); such a pair has capacity 0, is saturated by every coloring and is forced, so ratio 1 is the value consistent with 'the pairs with ratio 1 are exactly Q'; no zero-penalty instance is excluded
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 9, Lemma 3

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_WinWin
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 3 (p. 9): `cost(alg1) ≤ 2 · cost(F*) + q − 2 · sl`. -/
theorem lemma_3 (I : Instance) (R : PDRun I) (hR : IsPDRun I 1 0 R)
    (a : Finset (Fin I.n) → I.Pair → ℝ) (ha : R.IsBalanced 1 a)
    (Fs : Finset I.Edge) (hFs : I.IsForest Fs)
    (alg1 : Finset I.Edge) (h1 : I.IsMinimalConnecting alg1 (R.D' 1) R.finalForest) :
    I.cost alg1 ≤ 2 * I.cost Fs + R.qQ 1 a Fs - 2 * R.sl 1 a Fs := by sorry

end PCSFBreach.Main
