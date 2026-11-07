-- Prove2me | Theorems.Thm_StretchDepth_threshold_claim
-- name    : StretchDepth.threshold_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:37.966363+00:00
-- url     : https://prove2.me/theorems/66d3eb84-b1eb-455a-aa67-cce0fb6325a2
-- title:
--   Proof of Lemma 1 — the threshold claim
-- statement:
--   Let $d\ge1$, $0<\ell<N$, $\tau\ge0$ and $\alpha=(N-\ell)/((N/\ell)^d-1)$. Let $t_0=0,t_1,\dots,t_d$ be natural numbers. If $t_d\ge\tau$, then for some $1\le j\le d$,
--   $$
--   \ell t_j-Nt_{j-1}\ge\alpha\tau.
--   $$
--   Applied to the critical counts $t_j=t^G_j(\rho)$, this reduces a large total of critical queries to a single round where the Critical Query bound is strong.
--
--   Differences from the source:
--   - generalization: the critical counts t^G_j(rho) of a run → any sequence of naturals with t 0 = 0; reason: the claim is arithmetic, and the critical counts are such a sequence (crit at 0 rounds is 0)
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.17

import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Threshold claim.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.17: "Now, for some G, ρ and threshold τ ≥ 0, we claim that if
tG d (ρ) ≥ τ, then we must have that ℓtG j (ρ) − NtG j−1(ρ) ≥ ατ for some j."

**Formalization Note.** The claim is arithmetic: it is stated for any sequence of naturals with
`t 0 = 0`, which covers `j ↦ crit ρ G t j`. `0 < ℓ < N` holds in the page's setting. -/
theorem threshold_claim (N d : ℕ) (hd : 1 ≤ d) (ℓ τ : ℝ) (hℓ : 0 < ℓ) (hℓN : ℓ < N) (hτ : 0 ≤ τ)
    (t : ℕ → ℕ) (ht0 : t 0 = 0) (htd : τ ≤ t d) :
    ∃ j, 1 ≤ j ∧ j ≤ d ∧ alpha N ℓ d * τ ≤ ℓ * t j - (N : ℝ) * t (j - 1) := by sorry

end StretchDepth
