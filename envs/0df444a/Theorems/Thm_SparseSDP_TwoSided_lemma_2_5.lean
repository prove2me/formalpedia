-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_lemma_2_5
-- name    : SparseSDP.TwoSided.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:11.838648+00:00
-- url     : https://prove2.me/theorems/84303bf8-b3c1-4336-8b43-c7adaa0a8ae3
-- title:
--   Lemma 2.5, pp. 20–21 — the Lánczos upper certificate is one-sided and uses few products
-- statement:
--   Let $M$ be real symmetric with $\|M\|\le\omega$, and write $u=R\lambda_{\max}(M)$. For a sufficiently large constant $c_E$, every $\zeta>0$ and $\delta_{\mathrm{eig}}\in(0,1)$, the certificate program returns $\tilde u$ with
--   $$
--   u-\zeta\le\tilde u\le u
--   $$
--   with probability at least $1-\delta_{\mathrm{eig}}$. The right inequality holds on every tape. The program makes at most $k=\min\{d,\lceil c_E\sqrt{R\omega/\zeta}\log(d/\delta_{\mathrm{eig}})\rceil\}$ matrix–vector products, and its total cost is $O(k(T_M+d)+k^2+d)$ for a product of cost $T_M$.
--
--   The sign test of the search needs only this one-sided estimate.
--
--   Differences from the source:
--   - reading: $\tilde O(\min\{n+1,\sqrt{R\omega_D/\zeta}\})$ matrix–vector products (67) → $k$ iterations of the stated formula, with a cost bound in $k$; reason: [KW92] is not in this PDF; the logarithm $\log(d/\delta_{\mathrm{eig}})$ is the random-start one and $k$ is capped at the dimension
--   - generalization: $M_g$ of Eq. (65) with $\omega_D=2$, dimension $n+1$ → any symmetric $M$ with $\|M\|\le\omega$, any $\omega>0$, dimension $d$; reason: the proof uses only these properties; it specializes to $M_g$
--   - generalization: both inequalities with probability at least $1-\delta_{\mathrm{eig}}$ → the right inequality on every tape; reason: stated in the proof (p. 21): the upper bound follows from Rayleigh–Ritz
--   - encoding: the Ritz value → the primitive `tridiagLamMax`, charged $\ell^2$; reason: the paper leaves its cost unstated; it is of lower order
--   - encoding: with probability at least $1-p$ → the failure set has outer measure at most $p$ under `tapeLaw`; reason: no measurability of the event needs assuming; for a measurable event it is the same statement
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Lemma 2.5, pp. 20–21, Eqs. (65)–(70)

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_certProg

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Lemma 2.5** (Computable Upper Certificate), pp. 20–21.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Lemma 2.5, pp. 20–21.

`M` is the symmetric `M_g` of Eq. (65), with `‖M‖ ≤ ω` (`ω = ω_D`) and `u_g = R λmax(M)`.
The right inequality of (66) holds on every tape (Rayleigh–Ritz, p. 21); the left one fails with
probability at most `δ_eig`. The product count (67) is stated through the iteration count `k` of
`certIters`, for a sufficiently large constant `c_E`.

**Formalization Note.** `mv` is any charged product with `M`, of cost `TM`. -/
theorem lemma_2_5 : ∃ c₀ : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ (P : Consts), c₀ ≤ P.cE →
    ∀ (d : ℕ) (M : Mat d) (mv : Vec d → Prog (Vec d)) (TM R ω ζ δe : ℝ),
      1 ≤ d → M.IsHermitian → ‖M‖ ≤ ω → 0 < ω → 0 < R → 0 < ζ → 0 < δe → δe < 1 → 0 ≤ TM →
      Implements mv M TM →
      (∀ tape : Tape, runVal (certProg P R ω ζ δe mv) tape ≤ R * lamMax M) ∧
      tapeLaw {tape | ¬ R * lamMax M - ζ ≤ runVal (certProg P R ω ζ δe mv) tape} ≤
        ENNReal.ofReal δe ∧
      ∀ tape : Tape, (runCost (certProg P R ω ζ δe mv) tape : ℝ) ≤
        C * ((certIters P d R ω ζ δe : ℝ) * (TM + d) + (certIters P d R ω ζ δe : ℝ) ^ 2 + d + 1) := by sorry

end SparseSDP.TwoSided
