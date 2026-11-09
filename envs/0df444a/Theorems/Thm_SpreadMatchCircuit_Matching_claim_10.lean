-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_claim_10
-- name    : SpreadMatchCircuit.Matching.claim_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:12.614216+00:00
-- url     : https://prove2.me/theorems/04a69447-650e-4426-a14f-507b1ce34c09
-- title:
--   Claim 10 — the decoded matching keeps the residual: $\pi_\ell(z)\subseteq\pi_{\ell-1}(z')$
-- statement:
--   Let $Z\sim\mu$ be a random matching with $|Z|\le t$, $t>1$, and support $\mathcal Z$, let $0<\varepsilon<1/2$, $0<\gamma\le 1$, and let $\{W_{i,j}\}$ be a stage family for these parameters. Fix an ordering of all sets of edges. Let $\ell$ be a stage, $z\in\mathcal Z$, and $S\subseteq[n]$, $f:[n]\to[a]$. Suppose that $z$ satisfies the event $E_{\ell,a}$ and that $(\bar W_\ell,z)$ is consistent with $S,f$. If $z'$ is the matching decoded from $T=W_\ell\cup V(\pi_\ell(z))$, $S$, $f$, then
--
--   $$\pi_\ell(z)\subseteq\pi_{\ell-1}(z').$$
--
--   This is the step of the encoding argument that lets $\pi_\ell(z)$ be recovered from $\pi_{\ell-1}(z')$ with few extra bits: $z'$ is determined by $T$, so the number of possibilities for $\pi_\ell(z)$ is bounded by the number of subsets of $\pi_{\ell-1}(z')$.
--
--   **Formalization Note** The objects are those of the `Encoding` definition. The source's $k$ and $q$ here are $\ell$ and $\lceil\log_2 t\rceil$. The decoder uses $\emptyset$ as a total-function default. Under the stated event and consistency hypotheses its feasible family is nonempty, as the source observes; no additional feasibility hypothesis is imposed.
--
--   Differences from the source:
--   - generalization: lexicographic order on matchings → an arbitrary linear order on sets of edges; reason: the proof uses no property of the order, and the lexicographic order is an instance.
--   - generalization: the standing hypothesis that Z is r-spread → not assumed; reason: the claim is deterministic, and the source's setting is the case of an r-spread law.
--   - encoding: domains of ε and γ left implicit → 0 < ε < 1/2 and 0 < γ ≤ 1; reason: log(1/ε) and a set of size γn require them, and the source's use has them.
--   - reading: log of unspecified base → log₂ in ⌈log t⌉ and the natural log in J_i; reason: the dyadic thresholds need base 2 for the first, and the base of the second affects only universal constants.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 9, Claim 10

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Graphs
import Definitions.Def_SpreadMatchCircuit_Matching_SpreadLaw
import Definitions.Def_SpreadMatchCircuit_Matching_Encoding

namespace SpreadMatchCircuit.Matching

/-- Claim 10, p. 9: `π_ℓ(z) ⊆ π_{ℓ-1}(z')`, for `z'` the decoded matching. -/
theorem claim_10 {n : ℕ} (ord : LinearOrder (Finset (Edge n))) (μ : PMF (Finset (Edge n)))
    (t ε γ : ℝ) (ht : 1 < t) (hε₀ : 0 < ε) (hε : ε < 1 / 2) (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hμ : IsBoundedMatchingLaw μ t)
    (W : ℕ → ℕ → Finset (Fin n)) (hW : IsStageFamily t ε γ W)
    (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ₂ : ℓ ≤ numStages t ε)
    (z : Finset (Edge n)) (hz : z ∈ lawSupport μ)
    (a : ℕ) (S : Finset (Fin n)) (f : Fin n → Fin a)
    (hE : EventE ord (lawSupport μ) t ε W ℓ a z)
    (hD : IsConsistent ord (lawSupport μ) t ε W ℓ z S f) :
    residual ord (lawSupport μ) t ε W ℓ z ⊆
      residual ord (lawSupport μ) t ε W (ℓ - 1)
        (decode ord (lawSupport μ) t ε W ℓ
          (flatW t ε W ℓ ∪ verts (residual ord (lawSupport μ) t ε W ℓ z)) S f) := by sorry

end SpreadMatchCircuit.Matching
