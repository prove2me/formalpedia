-- Prove2me | Theorems.Thm_RobustQSC_avg_eq_one_sub_infMu
-- name    : RobustQSC.avg_eq_one_sub_infMu
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:28.42461+00:00
-- url     : https://prove2.me/theorems/4227bfa5-4cbb-4495-ada3-30457e01ecae
-- title:
--   Proof of Corollary 2, p.22 — $\mathrm{Avg}_f[g]=1-\frac1n\mathrm{Inf}_{\mu_f}[g/f]$
-- statement:
--   Let $n\ge1$ and let $f,g:\{0,1\}^n\to\mathbb C$ with $\|f\|_2=\|g\|_2=1$ and $f$ non-zero everywhere. Then
--
--   $$
--   \mathrm{Avg}_f[g]=1-\frac1n\mathrm{Inf}_{\mu_f}\Bigl[\frac gf\Bigr].
--   $$
--
--   This identity makes the uncertainty principle for Avg an uncertainty principle for harmonic-mean weighted total influence, and it is the win-win's "high influence" case.
--
--   Differences from the source:
--   - encoding: "and hence also for $\hat f$ and $\hat g$" → no second clause; reason: it is the instance $f:=\hat f$, $g:=\hat g$, since the Fourier transform is unitary
--   - encoding: $n$ implicit → $n\ge1$; reason: the formula has $1/n$; at $n=0$ Lean gives $0=1$, and the source has $n\ge1$ qubits
--   - encoding: the parenthetical "as long as $f$ and $\hat f$ are non-zero everywhere" → hypothesis $f(x)\ne0$ for every $x$; reason: $g/f$ is undefined where $f$ vanishes; the condition is the page's own
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), proof of Corollary 2, p.22; §2.5.3, p.15; Appendix C, pp.80–81

import Definitions.Def_RobustQSC_avg
import Definitions.Def_RobustQSC_infMu

namespace RobustQSC

open QAlgorithms

/-- **The Avg–Inf identity (proof of Corollary 2, p.22; Appendix C).** For all `f`, `g` with
`‖f‖₂ = ‖g‖₂ = 1` and `f` vanishing nowhere,
`Avg_f[g] = 1 − (1/n) Inf_{μ_f}[g/f]`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), proof of Corollary 2, p.22 ("This follows immediately from the identity Avg_f[g] =
1 − (1/n) Inf_{µf}[g/f], which holds for all f and g such that ‖f‖₂ = 1, ‖g‖₂ = 1, and hence also
for f̂ and ĝ (as long as f and f̂ are non-zero everywhere …)"), §2.5.3, p.15; Appendix C,
pp.80–81.

**Formalization Note.** The "hence also for f̂ and ĝ" clause is the instance `f := fourier f`,
`g := fourier g` (the Fourier transform is unitary), so no second clause is stated. `n ≥ 1`
(at `n = 0` the left side is `0` and the right side `1`). -/
theorem avg_eq_one_sub_infMu (n : ℕ) (hn : 1 ≤ n) (f g : EuclideanSpace ℂ (Qubits n))
    (hf : IsState f) (hg : IsState g) (hf0 : ∀ x, f x ≠ 0) :
    avg f g = 1 - infMu (muOf f) (fun x => g x / f x) / n := by sorry

end RobustQSC
