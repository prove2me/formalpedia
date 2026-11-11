-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_b9_dependent_lower
-- name    : ShuffleDecoys.Hierarchy.b9_dependent_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:38.44895+00:00
-- url     : https://prove2.me/theorems/2271685f-97a6-4b7c-8671-d6e84c994326
-- title:
--   Appendix B.9, proof of Theorem B.1 — under the uniform prior every mechanism leaks ≥ [log(d/n)]₊
-- statement:
--   Let $d,n\ge2$ and let $M$ be uniform on $[d]$. For every decoy mechanism (any conditional law of the $n-1$ decoys given $M$, so in particular every message-dependent one), the shuffled release satisfies
--   $$I_{U_d}(M;Z)\ \ge\ \big[\log(d/n)\big]_+,\qquad [x]_+:=\max\{x,0\},$$
--   with the natural logarithm. This lower-bounds the minimax leakage $L_{\mathrm{dep}}(d,n)$.
--
--   Differences from the source:
--   - encoding: the uniform prior $U_d$ → a law $U$ on `Fin d` with $U(m)=1/d$ for all $m$; reason: same law.
--   - reading: the chain "$I_{U_d}(M;Z)=\log d-H(M\mid Z)\ge\log d-\log\min\{d,n\}$" → only its conclusion is stated; reason: the intermediate steps are the proof.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 47, Appendix B.9, proof of Theorem B.1, 'Exact characterization of message-dependent decoys', lower bound

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Appendix B.9, proof of Theorem B.1, message-dependent lower bound: under the uniform prior
`U_d`, every mechanism (every decoy kernel) leaks `I_{U_d}(M; Z) ≥ [log(d/n)]₊` (nats). -/
theorem b9_dependent_lower (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (U : PMF (Fin d))
    (hU : ∀ m, U m = (d : ℝ≥0∞)⁻¹) (R : DecoyKernel (Fin d) n) :
    ENNReal.ofReal (max (Real.log ((d : ℝ) / n)) 0) ≤ leakage U R := by sorry

end ShuffleDecoys.Hierarchy
