-- Prove2me | Theorems.Thm_StretchDepth_claim_a
-- name    : StretchDepth.claim_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:23.372439+00:00
-- url     : https://prove2.me/theorems/d2e1e5a4-e9c3-40f4-bfe0-b48ed339f958
-- title:
--   Proof of Theorem 1, (a) — the test accepts all of $H^G$ and few strings
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $n<N$, $m<M$, $q,d\ge1$, $1\le s<2^n/q$, $p=s/2^n$, $\ell=n-\log_2(qs)$, and let $H$ be a $(q,d)$-construction with
--   $$
--   M\ge\bigl(m+C(1+\log_2 qd)\bigr)\Bigl(\frac{N}{\ell}\Bigr)^d.
--   $$
--   Sample $G$ uniformly and $S$ with inclusion probability $p$, and set $T=T_{G|_{\overline S}}$. Then
--   $$
--   \Pr_{G,T}\bigl[\mathrm{Adv}_{H^G}(T)\ge0.9\bigr]>\tfrac12.
--   $$
--   This is one half of the contradiction in the proof of Theorem 1: $T$ is a successful test against $H^G$ with high probability.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
--   - generalization: q >= 2 as in Theorem 1, with C log qd → q >= 1, with C(1 + log_2 qd); reason: for q >= 2, 1 + log_2 qd <= 2 log_2 qd, so the source form with constant 2C implies the hypothesis here
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.19

import Definitions.Def_StretchDepth_IsPRGReduction
import Definitions.Def_StretchDepth_testOf
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Proof of Theorem 1, (a).**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.19: "Assuming towards a contradiction that
M ≥ (m+C log qd)(N/(n−log qs))^d for a sufficiently large universal constant C, we will show that
when G, T are sampled in this way we have: (a) Pr_{G,T}[AdvHG(T) ≥ 0.9] > 1/2".

**Formalization Note.** `(G, T)` is sampled as `G` uniform, `S` with inclusion probability
`p = s/2^n`, `T = T_{G|_{S̄}}` (`freeOn`, `sampling_equivalence`). The constant has the form
`C(1 + log qd)` to fit `lemma_1`; it is the page's for `qd ≥ 2`, the case the goal uses. -/
theorem claim_a :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N m M q d : ℕ) (s : ℝ) (H : Bits m → RoundTree n N M),
      n < N → m < M → 1 ≤ q → 1 ≤ d → 1 ≤ s → (q : ℝ) * s < 2 ^ n → IsConstruction H q d →
      ((m : ℝ) + C * (1 + Real.logb 2 ((q : ℝ) * d))) * ((N : ℝ) / ell n q s) ^ d ≤ M →
      1 / 2 < probGS (s / 2 ^ n) (fun G S => 9 / 10 ≤ advH H G (testOf H (freeOn G S))) := by sorry

end StretchDepth
