-- Prove2me | Theorems.Thm_SustainableFashion_Variety_uniform_expectations
-- name    : SustainableFashion.Variety.uniform_expectations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:32.992979+00:00
-- url     : https://prove2.me/theorems/6e9912f9-99e1-4f71-8187-2b3fe92a46c8
-- title:
--   §3.2, p. 11 — for n ∼ U(0, n̄): E(n) = n̄/2 and E[(n − q)⁺] = (n̄ − q)²/(2n̄)
-- statement:
--   Let the market size $n$ be uniformly distributed on $[0,\bar n]$ with $\bar n>0$, and let $0\le q\le\bar n$. Then
--   $$\mathbb E(n)=\frac{\bar n}{2},\qquad \mathbb E[(n-q)^+]=\frac{(\bar n-q)^2}{2\bar n}.$$
--
--   These are the two expectations substituted into the expected profit to obtain problem (1); the second is the expected quick-response production when $q$ units of the trendy style are stocked.
--
--   **Formalization Note** The uniform law on $[0,\bar n]$ has density $1/\bar n$, so each expectation is written as an interval integral over $[0,\bar n]$ divided by $\bar n$, and $(n-q)^+=\max(n-q,0)$. The paper prints "$\mathbb E[(\bar n-q)^+]$", a slip for $\mathbb E[(n-q)^+]$; the statement uses the intended quantity.
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), §3.2, sentence preceding (1) ("After substituting E(n) = n̄/2 …"), p. 11

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

namespace SustainableFashion.Variety

theorem uniform_expectations (nbar q : ℝ) (hn : 0 < nbar) (hq0 : 0 ≤ q) (hq : q ≤ nbar) :
    (∫ n in (0 : ℝ)..nbar, n) / nbar = nbar / 2 ∧
    (∫ n in (0 : ℝ)..nbar, max (n - q) 0) / nbar = (nbar - q) ^ 2 / (2 * nbar) := by sorry

end SustainableFashion.Variety
