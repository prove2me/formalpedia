-- Prove2me | Theorems.Thm_SeedRecyclingDL_Codes_corollary_4_2
-- name    : SeedRecyclingDL.Codes.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:10.541232+00:00
-- url     : https://prove2.me/theorems/0395a0c5-3c55-4fcf-b0a2-bcd88620e480
-- title:
--   Corollary 4.2 — Payload competitors
-- statement:
--   For all binary $m$-bit payloads $x,x'$ and every common $N$-bit suffix $s$,
--   $$d_{\rm DL}(x\Vert s,x'\Vert s)=d_{\rm DL}(x,x').$$
--   For the radius-$t$ DL channel, the payload competitors defined by the existence of a confusable common suffix satisfy
--   $$\Gamma_E(x)=(B_{2t}(x)\cap\{0,1\}^m)\setminus\{x\}.$$
--   Both the distance identity and the exact set equality are asserted; competitor containment alone is insufficient.
--
--   Differences from the source:
--   - encoding: binary strings and one-based positions → lists of Fin 2 with length predicates and current-word zero-based positions; reason: the order-preserving representation includes empty intermediate words and every unrestricted DL script
--   - generalization: the standing error regime t at least 1 → the set identity also covers t=0; reason: the zero-error channel has no distinct competitors and all positive source budgets remain included
-- source:
--   Quan D. Bui, Manabu Hagiwara, Shuche Wang, Van Khu Vu, STOC 2027 submission #1449 (October 2026), Corollary 4.2, printed p. 11 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1449.pdf

import Definitions.Def_SeedRecyclingDL_Codes_Execution

set_option autoImplicit false

namespace SeedRecyclingDL.Codes

theorem corollary_4_2 (t m N : ℕ) :
    (∀ x x' s : Word, x.length = m → x'.length = m → s.length = N →
      distance (x ++ s) (x' ++ s) = distance x x') ∧
    (∀ x : Word, x.length = m → payloadCompetitors (dlChannel t) m N x = dlCompetitors t m x)
    := by sorry

end SeedRecyclingDL.Codes
