-- Prove2me | Theorems.Thm_SYKLearn_lemma_2_7
-- name    : SYKLearn.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:15:39.077516+00:00
-- url     : https://prove2.me/theorems/672342fb-aaa5-4cc7-8a04-3c1484d779e2
-- title:
--   Lemma 2.7 — basic norm bounds: $\|H(g)\|=O(n)$, $\|g\|_2\le2\sigma_n\sqrt m$, $\big|\|g\|_2^2/(\sigma_n^2m)-1\big|\le\tfrac14$
-- statement:
--   Let $H_g=\sum_{|I|=4}g_I\Gamma_I$ be the SYK Hamiltonian on $n$ Majorana modes with independent couplings $g_I\sim\mathcal N(0,\sigma_n^2)$, $\sigma_n^2=6/n^3$, and let $m=\binom n4$. There are universal constants $C,c>0$ such that, for all sufficiently large even $n$, except with probability at most $e^{-cn}$ over $g$,
--
--   $$\|H_g\|_{\rm op}\le Cn,\qquad \|g\|_2\le2\sigma_n\sqrt m,\qquad \Big|\frac{\|g\|_2^2}{\sigma_n^2m}-1\Big|\le\frac14 .$$
--
--   These are the typical-size facts used throughout: they place the scale $\alpha=\|g\|_2/(\sigma_n\sqrt m)$ in $[3/4,5/4]$ and bound the Hamiltonian's norm linearly in $n$.
--
--   **Formalization Note** $O(n)$ and $\Omega(n)$ are constants chosen before $n$; "sufficiently large" is $n\ge N_0$. The operator norm is the $\ell^2$ operator norm.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 2.7, p.16

import Mathlib
import Definitions.Def_SYKLearn_Basic

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 2.7 (Basic norm bounds)**, p.16 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning
SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let `m = C(n,4)`. For all
sufficiently large `n`, except with probability `e^{−Ω(n)}` over `g`,
`‖H(g)‖ ∈ O(n)`, `‖g‖₂ ≤ 2σ_n√m` and `|‖g‖₂²/(σ_n² m) − 1| ≤ 1/4`.

**Formalization Note.** `O(n)` and `Ω(n)` are universal constants `C, c > 0` chosen before `n`;
"sufficiently large" is `N ≥ N₀`. The operator norm is `SYKEdge.opNorm` (ℓ² operator norm, the
paper's `‖T‖ = ‖T‖_op`, Notation p.11). The exceptional set is bounded in outer measure. `N` even
and `N ≥ 4` come from `Model`; `Q.J = 1` makes the couplings `N(0, 6/N³)`. Statements are for every
CAR family (unitarily invariant). -/
theorem lemma_2_7 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ (N : ℕ) (Q : Model N), N₀ ≤ N → Q.J = 1 →
      disorderLaw Q {w | ¬ (SYKEdge.opNorm (hamiltonian Q w) ≤ C * N ∧
          cnorm w ≤ 2 * sigma N * Real.sqrt (m N) ∧
          |cnorm w ^ 2 / (sigma N ^ 2 * m N) - 1| ≤ 1 / 4)} ≤
        ENNReal.ofReal (Real.exp (-(c * N))) := by sorry

end SYKLearn
