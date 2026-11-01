-- Prove2me | Theorems.Thm_WeakSignalBandit_lemma_12
-- name    : WeakSignalBandit.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:55.050403+00:00
-- url     : https://prove2.me/theorems/d5f35686-4127-4342-bdcd-036e81db905d
-- title:
--   Lemma 12, p.33 — $p$-th moments and untruncated characteristics converging locally uniformly imply the truncated conditions (A.7)–(A.9)
-- statement:
--   Let $\Pi^n$ be transition (probability) kernels on $\mathbb R^d$ (Euclidean norm), $K^n=n\Pi^n$, and let $a_{k,l}$, $b_k$ be functions on $\mathbb R^d$. Fix $p\ge2$ and suppose that for all $R<\infty$ and all $k,l$,
--   $$\lim_{n\to\infty}\sup_{|z|<R}m^n_p(z)=0,\qquad\lim_{n\to\infty}\sup_{|z|<R}|\tilde a^n_{k,l}(z)-a_{k,l}(z)|=0,\qquad\lim_{n\to\infty}\sup_{|z|<R}|\tilde b^n_k(z)-b_k(z)|=0,$$
--   where $m^n_p(z)=\int|x-z|^pK^n(z,dx)$ and $\tilde a^n$, $\tilde b^n$ are the untruncated second and first moments of $K^n$. Then the truncated conditions (A.7)–(A.9) hold: for all $k,l$ and $\epsilon,R>0$, uniformly over $|z|<R$,
--   $$a^n_{k,l}(z)\to a_{k,l}(z),\qquad b^n_k(z)\to b_k(z),\qquad \Delta^n_\epsilon(z)\to0.$$
--
--   The lemma removes the truncation $|x-z|\le1$ from the hypotheses of Theorem 11, so that they can be checked by computing plain moments of the kernel (A.14).
--
--   **Formalization Note** $p$ is real. $m^n_p$ is valued in $[0,\infty]$, and its uniform convergence to $0$ is written as: for every $\epsilon>0$, eventually $m^n_p(z)\le\epsilon$ for all $|z|<R$.
--
--   Differences from the source:
--   - generalization: ℝ^d → EuclideanSpace ℝ ι for any finite index type ι; reason: ι = Fin d is the source's case
--   - encoding: for all R < ∞ → for all R > 0; reason: for R ≤ 0 the set {|z| < R} is empty and every condition holds trivially
--   - encoding: lim sup_{|z|<R} m^n_p(z) = 0 → for every ε > 0, eventually m^n_p(z) ≤ ε for all |z| < R, with m^n_p valued in [0, ∞]; reason: the same statement for a [0, ∞]-valued moment; an infinite moment is never read as 0
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, Lemma 12, p.33 (m^n_p, ã^n, b̃^n defined on p.32; (A.7)–(A.9) on p.32)

import Mathlib
import Definitions.Def_WeakSignalBandit_ChainCharacteristics

open MeasureTheory ProbabilityTheory Filter Topology

namespace WeakSignalBandit

/-- **Lemma 12 (removing the truncation).** Fix `p ≥ 2`. Let `Π^n` be transition kernels on `ℝ^d`
(here `ℝ^ι`), `K^n = nΠ^n`, and let `a_{k,l}`, `b_k` be functions on `ℝ^d`. Suppose that for all
`R < ∞`, uniformly over `|z| < R`: the `p`-th moments `m^n_p(z) = ∫ |x − z|^p K^n(z, dx)` tend
to `0` (A.11), the untruncated second moments `ã^n_{k,l} → a_{k,l}` (A.12), and the untruncated
first moments `b̃^n_k → b_k` (A.13). Then the convergence in (A.7) through (A.9) holds: uniformly
over `|z| < R`, `a^n_{k,l} → a_{k,l}`, `b^n_k → b_k` and `Δ^n_ε → 0`, for all `k, l` and
`ε, R > 0`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, Lemma 12, p.33 (functions `m^n_p`, `ã^n`, `b̃^n` defined on p.32; (A.7)–(A.9)
on p.32).

**Formalization Note** `p` is real. `m^n_p` takes values in `[0, ∞]`, and (A.11) is written as
"for every `ε > 0`, eventually `m^n_p(z) ≤ ε` for all `|z| < R`", so an infinite moment is never
read as `0`. -/
theorem lemma_12 {ι : Type*} [Fintype ι]
    (T : ℕ → Kernel (Sp ι) (Sp ι)) [∀ n, IsMarkovKernel (T n)]
    (a : Sp ι → ι → ι → ℝ) (b : Sp ι → ι → ℝ) (p : ℝ) (hp : 2 ≤ p)
    (h11 : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ z : Sp ι, ‖z‖ < R → momentP (scaledKernel (T n) n) p z ≤ ENNReal.ofReal ε)
    (h12 : ∀ R : ℝ, 0 < R → ∀ k l,
      TendstoUniformlyOn (fun n z => fullDiff (scaledKernel (T n) n) z k l)
        (fun z => a z k l) atTop (Metric.ball 0 R))
    (h13 : ∀ R : ℝ, 0 < R → ∀ k,
      TendstoUniformlyOn (fun n z => fullDrift (scaledKernel (T n) n) z k)
        (fun z => b z k) atTop (Metric.ball 0 R)) :
    (∀ R : ℝ, 0 < R → ∀ k l,
      TendstoUniformlyOn (fun n z => truncDiff (scaledKernel (T n) n) z k l)
        (fun z => a z k l) atTop (Metric.ball 0 R)) ∧
    (∀ R : ℝ, 0 < R → ∀ k,
      TendstoUniformlyOn (fun n z => truncDrift (scaledKernel (T n) n) z k)
        (fun z => b z k) atTop (Metric.ball 0 R)) ∧
    (∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      TendstoUniformlyOn (fun n z => jumpMass (scaledKernel (T n) n) ε z)
        (fun _ => 0) atTop (Metric.ball 0 R)) := by sorry

end WeakSignalBandit
