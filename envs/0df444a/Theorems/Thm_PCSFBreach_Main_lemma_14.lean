-- Prove2me | Theorems.Thm_PCSFBreach_Main_lemma_14
-- name    : PCSFBreach.Main.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:58:03.151554+00:00
-- url     : https://prove2.me/theorems/8eec6b2a-0f34-4531-9ecb-332d5dc12ad5
-- title:
--   Lemma 14 — refinement into sets of size ≤ k with st ≤ (1 + 1/⌊log₂ k⌋)·st and equal gain
-- statement:
--   Consider a run of the primal-dual algorithm with $\lambda=2$, $\mu=10^{-12}$ on a PCSF instance, and let $k\ge 2$ be an integer. For every collection $\mathcal S$ of actively connected sets there is a collection $\mathcal S_k$ of actively connected sets such that
--   1. $|S|\le k$ for every $S\in\mathcal S_k$;
--   2. $\mathrm{st}(\mathcal S_k)\le\Big(1+\dfrac{1}{\lfloor\log_2 k\rfloor}\Big)\mathrm{st}(\mathcal S)$;
--   3. $\mathrm{gain}(\mathcal S_k)=\mathrm{gain}(\mathcal S)$.
--
--   It rests on the Borchers–Du decomposition of a Steiner tree into small full components and lets Lemma 6 restrict attention to collections of bounded-size sets.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: the run of §4–§8 on a fresh instance (λ = 2, µ = 10^-12, p. 12) → every run with IsPDRun I 2 (1/10^12) R; reason: the section's standing parameters, kept as printed
--   - encoding: the run of the primal-dual algorithm (§2) → every record R : PDRun I with IsPDRun I λ μ R (event times 0 = t_0 < … < t_len, forests F_k, active moats A_k ⊇ normal-active moats N_k, obeying the §2 rules at every time); reason: the algorithm is continuous-time; moats and duals are determined by the instance and only the choice among simultaneously tight edges varies, so the statement is made for every run
--   - encoding: ∫_0^∞ … dt of a quantity of A_t → the finite sum over the stages [t_k, t_{k+1}) of the run of the stage length times the quantity; reason: A_t is constant on each stage and empty from the final time on, so the integral is that finite sum (no Bochner-integral junk values)
--   - reading: ⌊log k⌋ → ⌊log₂ k⌋ (Nat.log 2 k); reason: Borchers–Du's k-restricted Steiner ratio is 1 + 1/⌊log₂ k⌋; with the natural logarithm the bound is undefined at k = 2 (⌊ln 2⌋ = 0); the base-2 reading is the stronger one for k ≥ 2
--   - encoding: st(S), cost of a minimum Steiner tree connecting S → minimum cost of an edge set connecting all vertices of S; reason: with nonnegative costs a cheapest connecting edge set contains a spanning tree of its component of the same cost
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 50, Lemma 14

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_PrimalDual
import Definitions.Def_PCSFBreach_Main_ActiveConn
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Lemma 14 (p. 50): every collection of actively connected sets can be refined into one with
sets of size at most `k`, Steiner cost at most `(1 + 1/⌊log₂ k⌋)` times larger, and the same gain. -/
theorem lemma_14 (k : ℕ) (hk : 2 ≤ k) (I : Instance) (R : PDRun I)
    (hR : IsPDRun I 2 (1 / 10 ^ 12) R)
    (𝒮 : Finset (Finset (Fin I.n))) (h𝒮 : R.IsActConnColl 𝒮) :
    ∃ 𝒮k : Finset (Finset (Fin I.n)), R.IsActConnColl 𝒮k ∧ (∀ S ∈ 𝒮k, S.card ≤ k) ∧
      I.stColl 𝒮k ≤ (1 + 1 / (Nat.log 2 k : ℝ)) * I.stColl 𝒮 ∧
      R.gain 𝒮k = R.gain 𝒮 := by sorry

end PCSFBreach.Main
