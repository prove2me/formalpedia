-- Prove2me | Theorems.Thm_StretchDepth_claim_b
-- name    : StretchDepth.claim_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:39.479098+00:00
-- url     : https://prove2.me/theorems/411d7af9-9278-462c-a19e-775f778dc933
-- title:
--   Proof of Theorem 1, (b) — the reduction fails on the sampled test
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $n<N$, $m<M$, $q_R,q_H\ge1$, $0<\epsilon\le1$, and let $q=\max(q_R,q_H)$. Let $s\ge Cq^2/\epsilon$ with $p=s/2^n\le1$. Let $H$ be a query procedure with at most $q_H$ queries on every oracle, and $R$ a randomized query procedure with at most $q_R$ queries in total, such that $\mathrm{SAdv}_G(R^{G,T})\ge0$ for all $G,T$. Sample $G$ uniformly, $S$ with inclusion probability $p$, and set $T=T_{G|_{\overline S}}$. Then
--   $$
--   \Pr_{G,T}\bigl[\mathrm{SAdv}_G(R^{G,T})<\epsilon\bigr]>\tfrac12.
--   $$
--   This is the other half of the contradiction: on the same distribution for which $T$ breaks $H^G$, the reduction fails to break $G$. The depth of $H$ plays no part in this half.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
--   - encoding: a randomized query procedure with q queries on every input and all randomness → a PMF over functions to decision trees, with the bound on real pairs (G, T) and on the support; reason: the procedures with at most q queries form a finite set after pruning unreachable branches, and only runs on real pairs matter to the definition
--   - generalization: the setting of Theorem 1: one q, H a (q, d)-construction, s from the contradiction hypothesis on M → separate qR, qH, no depth bound, no condition on M, only p <= 1 on s; reason: p.11 says this part does not use depth, and the rest is not used; q = max(qR, qH) specializes to the source
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, pp.19–21

import Definitions.Def_StretchDepth_IsPRGReduction
import Definitions.Def_StretchDepth_testOf

namespace StretchDepth

/-- **Proof of Theorem 1, (b).**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.19: "(b) Pr_{G,T}[SAdvG(RG,T ) < ϵ] > 1/2", with p.21: "We can strictly
upper bound the final value by ϵ/2 provided s ≥ Cq2/ϵ for a sufficiently large universal constant C."

**Formalization Note.** `(G, T)` is sampled as in `claim_a`. `R` has nonnegative signed advantage,
as Lemma 3 arranges. The query bounds `qR`, `qH` are separate, with `q = max(qR, qH)`, because
Lemma 3 changes only `R`. The depth `d` plays no part (p.11). `s` is only required to give
`p ≤ 1`: the condition `qs < 2^n` of Lemma 1 is not needed here. -/
theorem claim_b :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N m M qR qH : ℕ) (ε s : ℝ) (H : Bits m → RoundTree n N M)
      (R : PMF (Bits N → QProc n N M)),
      n < N → m < M → 1 ≤ qR → 1 ≤ qH → 0 < ε → ε ≤ 1 →
      C * ((max qR qH : ℕ) : ℝ) ^ 2 / ε ≤ s → s / 2 ^ n ≤ 1 →
      WithinQueries R qR → (∀ (G : Bits n → Bits N) (x : Bits m), numQueries G (H x) ≤ qH) →
      (∀ (G : Bits n → Bits N) (T : Bits M → Bool), 0 ≤ SAdv R G T) →
      1 / 2 < probGS (s / 2 ^ n) (fun G S => SAdv R G (testOf H (freeOn G S)) < ε) := by sorry

end StretchDepth
