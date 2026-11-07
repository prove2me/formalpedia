-- Prove2me | Theorems.Thm_RevisitXor_inner_form_corr
-- name    : RevisitXor.inner_form_corr
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:18.325445+00:00
-- url     : https://prove2.me/theorems/5644224b-9899-4dcd-96fc-cc6df27fc13b
-- title:
--   First observation: $x\cdot y'+x'\cdot y$ has correlation $1/M$ with $f_\pi(x,y)+f_\pi(x',y')$
-- statement:
--   Let $M=2^m$ and let $\pi$ be a fixed-point-free involution of $[2]^m$. The quadratic polynomial modulo $2$
--
--   $$p:[2]^{4m}\ni(x,y,x',y')\mapsto x\cdot y'+x'\cdot y\in[2]$$
--
--   has correlation exactly $1/M$ with $f_\pi(x,y)+f_\pi(x',y')$:
--
--   $$\operatorname{corr}\big(f_\pi(x,y)+f_\pi(x',y'),\;x\cdot y'+x'\cdot y\big)=\frac1M .$$
--
--   This is clause 3 of Theorem 1 for $k=2$: $f_\pi^{\oplus2}$ correlates $2^{-n/2}$ with a fixed quadratic polynomial, whatever $\pi$ is.
--
--   **Formalization Note** The input $(x,y,x',y')$ is the pair $((x,y),(x',y'))$. At $m=0$ there is no such $\pi$.
--
--   Differences from the source:
--   - generalization: has correlation ≥ 1/M → signed correlation = 1/M; reason: the proof's last sentence "Hence the correlation equals P[π(y) = y′] which is 1/M"; equality of the signed value implies ≥ 1/M with or without |·|
--   - encoding: (x, y, x′, y′) ∈ [2]^{4m} → ((x, y), (x′, y′)) ∈ ([2]^m × [2]^m) × ([2]^m × [2]^m); reason: same points
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), §1, p.6

import Mathlib
import Definitions.Def_RevisitXor_corr
import Definitions.Def_RevisitXor_mm

namespace RevisitXor

open OAI.MatchingSmoothing

/-- **First observation: correlation `1/M` with `x.y′ + x′.y`.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), §1, p.6: "First we note that, for every π, the quadratic polynomial modulo 2
p : [2]^{4m} ∋ (x, y, x′, y′) → x.y′ + x′.y ∈ [2] has correlation ≥ 1/M with fπ(x, y) + fπ(x′, y′)."
The proof ends "Hence the correlation equals P[π(y) = y′] which is 1/M."

**Formalization Note.** Stated as the equality `corr = 1/M` (`M = 2^m`) of the signed
correlation, which implies the printed `≥ 1/M` with or without absolute value. The input
`(x, y, x′, y′) ∈ [2]^{4m}` is `((x, y), (x′, y′))`. At `m = 0` there is no fixed-point-free
involution, and the statement is vacuous. -/
theorem inner_form_corr (m : ℕ) (π : Pairing (Cube m)) :
    corr (fun q : (Cube m × Cube m) × (Cube m × Cube m) => mm π q.1 + mm π q.2)
        (fun q => q.1.1 ⬝ᵥ q.2.2 + q.2.1 ⬝ᵥ q.1.2) = 1 / (2 : ℝ) ^ m := by sorry

end RevisitXor
