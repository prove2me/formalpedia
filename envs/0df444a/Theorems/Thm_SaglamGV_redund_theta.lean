-- Prove2me | Theorems.Thm_SaglamGV_redund_theta
-- name    : SaglamGV.redund_theta
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:12.982233+00:00
-- url     : https://prove2.me/theorems/a6d8c183-b755-4a8f-a7c2-85032e7965f0
-- title:
--   $R=\ln(2^n/V)=\Theta(n)$ for $1\le w\le(1/2-\varepsilon)n$
-- statement:
--   Fix $\varepsilon>0$. There is a constant $a>0$, depending only on $\varepsilon$, such that for all integers $n\ge1$ and $w$ with $1\le w\le(1/2-\varepsilon)n$, writing $d=w+1$, $V=|B_d|$ and $R=\ln(2^n/V)$,
--
--   $$
--   a\,n\le R\le n\ln 2 .
--   $$
--
--   So the redundancy is linear in the block length throughout the regime of the paper. The upper bound is used in §3.3 in the form $\tau<R\le n\ln2<n$.
--
--   Differences from the source:
--   - generalization: the regime ln n ≪ w ≤ (1/2 − ε)n → every n ≥ 1 and 1 ≤ w ≤ (1/2 − ε)n, with no growth condition on w; reason: the bound needs only V ≥ 1 and w ≤ (1/2 − ε)n; the paper's regime implies 1 ≤ w
--   - encoding: w = d − 1 → d = w + 1 with w : ℕ; reason: avoids natural-number subtraction; same instances
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.2 ("Our assumptions imply R = Θ(n)"); upper bound used on p.4 ("τ < R ≤ n ln 2 < n")

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Params

namespace SaglamGV

/-- $R = Θ(n)$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.2: "Our assumptions imply R = Θ(n)"; the upper bound $R ≤ n \ln 2$ is
used again on p.4: "τ < R ≤ n ln 2 < n").

For every $ε > 0$ there is $a > 0$ such that $a n ≤ R ≤ n \ln 2$ whenever $1 ≤ w ≤ (1/2 − ε)n$,
where $d = w + 1$ and $R = \ln(2^n/V)$.

**Formalization Note** The paper's regime is $\ln n ≪ w ≤ (1/2 − ε)n$; the statement only needs
$w ≥ 1$ (so that $V ≥ 1$), which that regime implies. -/
theorem redund_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ n w : ℕ, 1 ≤ n → 1 ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      a * n ≤ redund n (w + 1) ∧ redund n (w + 1) ≤ n * Real.log 2 := by sorry

end SaglamGV
