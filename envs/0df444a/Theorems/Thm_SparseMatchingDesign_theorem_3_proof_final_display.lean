-- Prove2me | Theorems.Thm_SparseMatchingDesign_theorem_3_proof_final_display
-- name    : SparseMatchingDesign.theorem_3_proof_final_display
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:48.804509+00:00
-- url     : https://prove2.me/theorems/1493dbc3-5803-4d41-b47c-048a0c9570a5
-- title:
--   Proof of Theorem 3 — $L(R_{n,K})\le\mathbb E[X]=\frac nK q^K=\frac{3n}{d+1}q^{(d+1)/3}=\frac{3n}{d+1}e^{-\gamma_2(d+1)}$
-- statement:
--   Let $K\ge1$ divide $n$, let $p\in(0,1)$, $q=1-p$, $d=3K-1$ and $\gamma_2=\tfrac13\log(1/q)$. The matching loss of the $K$-ring against $G^{\rm in}=K_n$ satisfies
--   $$L(R_{n,K})\le\mathbb E[X]=\sum_{i=1}^{n/K}\mathbb E[I_i]=\frac nK\,q^K=\frac{3n}{d+1}\,q^{(d+1)/3}=\frac{3n}{d+1}\,e^{-\gamma_2(d+1)},$$
--   where $X$ is the number of empty residual sub-clusters and $I_i$ the indicator that sub-cluster $i$ is empty. This is the last step of the proof of Theorem 3.
--
--   Differences from the source:
--   - encoding: expectation over the random surviving set; n/K → finite sum over subsets weighted by p^{|S|}(1 − p)^{n − |S|}; n/K as the real quotient (n : ℝ) / K; reason: same distribution; K ∣ n so the real and natural quotients agree
--   - encoding: G^in = Kₙ (§5) → matchingLoss p ⊤ (kRing n K); reason: ⊤ is the complete graph
--   - encoding: p ∈ (0,1) (§2.2, p.6) → hypotheses 0 < p and p < 1; reason: the paper's standing assumption
--   - encoding: standing assumptions K, m ∈ ℕ with n = Km (§2.1) and n a multiple of K (footnote 5, p.19) → hypotheses 0 < K and K ∣ n; reason: the paper's convention, written into the binders
--   - encoding: nodes [n], clusters ⌈i/K⌉ ∈ [n/K], the K-ring of eq. (6) → Fin n with paper node i = index i − 1, 0-based clusters i / K, eq. (6) applied to both orders of a pair; reason: a relabelling; same graphs
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §EC.4, proof of Theorem 3, final display, p.ec8 (pdf p.51)

import Mathlib
import Definitions.Def_SparseMatchingDesign_expectation
import Definitions.Def_SparseMatchingDesign_matchingLoss
import Definitions.Def_SparseMatchingDesign_kRing
import Definitions.Def_SparseMatchingDesign_subCluster
import Definitions.Def_SparseMatchingDesign_emptySubClusterCount

namespace SparseMatchingDesign

/-- **Proof of Theorem 3, final display.** The matching loss of the `K`-ring (against the input
graph `Kₙ`) is at most the expected number `E[X]` of empty residual sub-clusters, and
`E[X] = Σ_{i=1}^{n/K} E[I_i] = (n/K)·q^K = 3n/(d+1)·q^{(d+1)/3} = 3n/(d+1)·e^{−γ₂(d+1)}` with
`q = 1 − p`, `d = 3K − 1` and `γ₂ = (1/3) log(1/q)`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §EC.4, p.ec8: "We are now ready to prove Theorem 3. By Claims EC.3 and EC.4,
L(R_{n,K}) ≤ E[X] = Σ_{i=1}^{n/K} E[I_i] = n/K · q^K = 3n/(d+1) q^{(d+1)/3} = 3n/(d+1) e^{−γ₂(d+1)},
where the last two equalities follow from the facts that d = 3K − 1 and γ₂ = 1/3 log(1/q)."

**Formalization Note** `E` is the finite-sum expectation over the surviving set with survival
probability `p ∈ (0,1)` (§2.2, p.6); `I_s` is the indicator of `C̃_s = ∅` (0-based `s`). `n/K`
is the real quotient `(n : ℝ) / K`, equal to the natural one since `K ∣ n`. `d` is written
`(3 * K - 1 : ℝ)` and `q^{(d+1)/3}` is a real power. `K ≥ 1` and `K ∣ n` are the paper's
standing assumptions (footnote 5, p.19). -/
theorem theorem_3_proof_final_display (n K : ℕ) (hK : 0 < K) (hKn : K ∣ n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) :
    matchingLoss p ⊤ (kRing n K) ≤ expectation n p (fun S => (emptySubClusterCount K S : ℝ)) ∧
    expectation n p (fun S => (emptySubClusterCount K S : ℝ)) =
      ∑ s ∈ Finset.range (n / K),
        expectation n p (fun S => if subCluster K S s = ∅ then (1 : ℝ) else 0) ∧
    ∑ s ∈ Finset.range (n / K),
        expectation n p (fun S => if subCluster K S s = ∅ then (1 : ℝ) else 0) =
      (n : ℝ) / K * (1 - p) ^ K ∧
    (n : ℝ) / K * (1 - p) ^ K =
      3 * (n : ℝ) / ((3 * K - 1 : ℝ) + 1) * (1 - p) ^ (((3 * K - 1 : ℝ) + 1) / 3) ∧
    3 * (n : ℝ) / ((3 * K - 1 : ℝ) + 1) * (1 - p) ^ (((3 * K - 1 : ℝ) + 1) / 3) =
      3 * (n : ℝ) / ((3 * K - 1 : ℝ) + 1) *
        Real.exp (-((1 / 3) * Real.log (1 / (1 - p))) * ((3 * K - 1 : ℝ) + 1)) := by sorry

end SparseMatchingDesign
