-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_Supplement_zpp_upper_bound
-- name    : WatsonPseudodeterminism.MASeparation.Supplement.zpp_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:31:09.123988+00:00
-- url     : https://prove2.me/theorems/1897c8ef-479a-40d6-ba60-4fa16a7810ef
-- title:
--   §3 — Logarithmic RP cost of the §3 function and of its complement
-- statement:
--   Let $F_n=f\circ g^n$ be the §3 function with $h=100\lceil\log_2 n\rceil$, over the sizes $n=4s^2$, $s\ge1$, and let $\overline{F_n}$ be its complement. There is one natural constant $C$ such that for every such $n$ there is a natural $d$ with
--   $$d\le C\,(\lceil\log_2 n\rceil+1),$$
--   such that both $F_n$ and $\overline{F_n}$ have RP-type protocols of cost $d$: completeness $2/3$ on valid 1-inputs and acceptance probability exactly $0$ on valid 0-inputs.
--
--   This is the "$F\in\mathrm{ZPP}$" half of Theorem 1, via $\mathrm{ZPP}=\mathrm{RP}\cap\mathrm{coRP}$.
--
--   Differences from the source:
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; this is the base mission's published gadget length, rounding upward preserves the small-discrepancy regime
--   - reading: the implicit sizes n for which n/2 and √n are integers in §3 → n = 4s² for a positive natural s (base predicate Admissible); reason: §3 splits z into halves of length n/2 and flips √n bits per safe iteration; this fixes one infinite sequence on which both are integral
--   - encoding: O(log n) cost for the RP protocols of F and F̄ → one natural C with a common cost d ≤ C(clog₂ n + 1) for both; reason: the additive one covers short lengths without changing the logarithmic order; a protocol of smaller depth also has any larger depth bound
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §3, "F ∈ ZPP", p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_Models
import Definitions.Def_WatsonPseudodeterminism_MASeparation_Supplement_ZPPFunction

namespace WatsonPseudodeterminism.MASeparation.Supplement

/-- §3, p. 8, "F ∈ ZPP": uniform O(log n) RP-type cost for F and for its complement F̄. -/
theorem zpp_upper_bound :
    ∃ C : ℕ, ∀ n : ℕ, Admissible n → ∃ d : ℕ,
      d ≤ C * (Nat.clog 2 n + 1) ∧
      RPProtocol (zppLiftedFn n) d ∧ RPProtocol (complementFn (zppLiftedFn n)) d := by sorry

end WatsonPseudodeterminism.MASeparation.Supplement
