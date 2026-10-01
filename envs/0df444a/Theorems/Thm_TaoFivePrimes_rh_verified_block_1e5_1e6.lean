-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_block_1e5_1e6
-- name    : TaoFivePrimes.rh_verified_block_1e5_1e6
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-30T14:24:21.173074+00:00
-- url     : https://prove2.me/theorems/4734b6cf-ab60-4486-bf2b-a339b651f08d
-- title:
--   RH verified for $10^5 \le \operatorname{Im}(s) \le 10^6$
-- statement:
--   **Riemann hypothesis on the slab $10^5 \le \operatorname{Im}(s) \le 10^6$.** Let $s\in\mathbb C$ be a zero of the Riemann zeta function, $\zeta(s)=0$, lying in the open critical strip $0<\operatorname{Re}(s)<1$ with imaginary part in the range
--
--   $$10^5 \;\le\; \operatorname{Im}(s) \;\le\; 10^6.$$
--
--   Then $s$ lies on the critical line: $\operatorname{Re}(s)=\tfrac12$.
--
--   This is one block of the numerical verification of the Riemann hypothesis up to height $T_0=3.29\times10^9$ (Theorem 1.5 of Tao's five-primes paper). The slabs $[14,10^2],[10^2,10^3],\dots,[10^8,10^9],[10^9,3.29\cdot10^9]$, together with the zero-free range $0\le\operatorname{Im}(s)\le 14$, cover the whole range $0\le \operatorname{Im}(s)\le T_0$; each slab is an independent, finite computation (e.g. sign changes of Hardy's $Z$-function combined with Turing's method), so it can be certified separately.
--
--   **Formalization Note** The zero is not assumed simple; only its location is asserted. Endpoints of the slab are included, so consecutive slabs overlap in a line.
-- source:
--   D. J. Platt, Isolating some non-trivial zeros of zeta, Mathematics of Computation 86 (2017), 2449-2467 (rigorous verification of RH up to height 3.0610046e10); quoted as Theorem 1.5 (p. 7) of T. Tao, Every odd number greater than 1 is the sum of at most five primes, Math. Comp. 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, which also cites the independent verifications of van de Lune-te Riele-Winter (1986), Wedeniwski (ZetaGrid) and Gourdon (2004). This node is the restriction of that verified statement to one horizontal slab of the critical strip.

import Mathlib

namespace TaoFivePrimes

theorem rh_verified_block_1e5_1e6 (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (ha : 10 ^ 5 ≤ s.im) (hb : s.im ≤ 10 ^ 6) : s.re = 1 / 2 := by
  sorry

end TaoFivePrimes
