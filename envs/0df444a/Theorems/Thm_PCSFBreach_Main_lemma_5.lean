-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_5
-- name    : PCSFBreach.Main.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:58:14.262798+00:00
-- url     : https://prove2.me/theorems/c263e6fd-b1fe-4413-a406-dd37be9cf7dc
-- title:
--   Lemma 5 — cost(alg3) ≤ (2 − 2δ/3)·cost(F*) + (K − 2 + 2δ/3)·p − (1 − 2δ/3)·q
-- statement:
--   Run the primal-dual algorithm with $\lambda=1$, $\mu=0$ on a PCSF instance $I$, let $Q$ be the forced pairs and $a$ a balanced coloring. Let $\delta=10^{-18}$, $K=10^6+2$, let $B$ be any algorithm with the bifactor guarantee of Theorem 2 for these constants, and let $\mathrm{alg}_3=B(I|_{D\setminus Q})$. For every forest $F^*$ of $I$, with $p$, $q$ the quantities of §3,
--   $$\mathrm{cost}(\mathrm{alg}_3)\le\Big(2-\tfrac23\delta\Big)\mathrm{cost}(F^*)+\Big(K-2+\tfrac23\delta\Big)p-\Big(1-\tfrac23\delta\Big)q ,$$
--   cost evaluated with respect to the original pair set $D$.
--
--   This is the third candidate bound; it supplies the improvement when $p$ is small.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - generalization: the balanced coloring fixed with Lemma 1(iv) → every balanced coloring a of the run (IsBalanced); reason: the proof uses only feasibility and the balanced property; the computed coloring is one balanced coloring
--   - generalization: F* an optimal solution → F* any forest of the instance; reason: the proof never uses optimality of F*; an optimal forest is a forest
--   - generalization: alg3 = the bifactor algorithm of Theorem 2 applied to the instance with pair set D \ Q → B applied to that instance, for any map B from instances to edge sets with the bifactor guarantee of Theorem 2 (δ = 10^-18, K = 10^6 + 2) on every instance with real data; reason: the proof uses only this guarantee; the bifactor algorithm has it (milestone theorem_2)
--   - encoding: Q = {i ∈ D : r_i = 1} (Algorithm 1, line 2) → Q = the forced pairs of the run (§2.1, p. 6); reason: the two sets coincide for a balanced coloring by Lemma 1(iv); §3's analysis (p. 8) takes Q from the primal-dual run
--   - encoding: r_i = l_i/(λπ_i) → r_i = l_i/(λπ_i) when π_i > 0, and r_i := 1 when π_i = 0; reason: the paper removes pairs with π_i = 0 without loss of generality (p. 4); such a pair has capacity 0, is saturated by every coloring and is forced, so ratio 1 is the value consistent with 'the pairs with ratio 1 are exactly Q'; no zero-penalty instance is excluded
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 11, Lemma 5

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_WinWin
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 5 (p. 11): `cost(alg3) ≤ (2 − (2/3)δ) cost(F*) + (K − 2 + (2/3)δ) p − (1 − (2/3)δ) q`,
with `δ = 10⁻¹⁸`, `K = 10⁶ + 2`, where `alg3` is the output of the bifactor algorithm of Theorem 2
on the instance with pair set `D \ Q`. -/
theorem lemma_5 (B : (J : Instance) → Finset J.Edge) (hB : IsBifactor (1 / 10 ^ 18) (10 ^ 6 + 2) B)
    (I : Instance) (R : PDRun I) (hR : IsPDRun I 1 0 R)
    (a : Finset (Fin I.n) → I.Pair → ℝ) (ha : R.IsBalanced 1 a)
    (Fs : Finset I.Edge) (hFs : I.IsForest Fs) :
    I.cost (I.liftEdges (Finset.univ \ R.Q 1) (B (I.restrictPairs (Finset.univ \ R.Q 1)))) ≤
      (2 - (2 / 3) * (1 / 10 ^ 18)) * I.cost Fs
        + ((10 ^ 6 + 2) - 2 + (2 / 3) * (1 / 10 ^ 18)) * R.pD 1 Fs
        - (1 - (2 / 3) * (1 / 10 ^ 18)) * R.qQ 1 a Fs := by sorry

end PCSFBreach.Main
