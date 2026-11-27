-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_4_4
-- name    : SinkhornHall.Supplement.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:11:11.245861+00:00
-- url     : https://prove2.me/theorems/ebe81844-4aa1-42a2-b77b-63b50f1575d1
-- title:
--   Lemma 4.4 — if $\|p^*-p\|_\infty<1/(2n^2)$, every sort of $p$ has every $X_\kappa$ as a prefix
-- statement:
--   Setting of §4: $A$ is a nonnegative $n\times n$ matrix with no zero row or column (its support graph $G=G(A)$ has no isolated node), the marginals are $(r,c)=(\mathbf 1,\mathbf 1)$, $A_{\max}$ is the largest entry and $A_{\min}$ the least positive entry of $A$, and $(M_k,N_k)$ is the Sinkhorn sequence $N_0=C(A)$, $M_k=R(N_k)$, $N_{k+1}=C(M_k)$. Let $N^*$ be the limit of $N_k$, $p^*=N^*\mathbf 1$, and let $X_0\supset X_1\supset\dots\supset X_\theta$ be the extreme stable sets' row parts, ordered as in §3 (for $(r,c)=(\mathbf 1,\mathbf 1)$).
--
--   Let $p\in\mathbb R^n$ satisfy
--
--   $$\|p^*-p\|_\infty<\frac1{2n^2},$$
--
--   and let $p_{i_1}\le p_{i_2}\le\dots\le p_{i_n}$ be any sort of $p$. Then the output $U_k=\{i_1,\dots,i_k\}$ ($k=0,\dots,n$) contains $X_\kappa$ for every $\kappa=0,1,\dots,\theta$: each $X_\kappa$ equals some $U_k$.
--
--   In step 2 of Sinkhorn & Sorting Marginals, $p$ is the row-sum vector of $N_\ell$.
--
--   Differences from the source:
--   - generalization: $p=A\mathbf 1$ at step 2 of the algorithm → any vector $p\in\mathbb R^n$ with $\|p^*-p\|_\infty<1/(2n^2)$; reason: the proof uses only the accuracy hypothesis; the step-2 vector is a special case
--   - encoding: the output contains $X_\kappa$ → for every tie-break $\sigma$ of the sort ($p\circ\sigma$ monotone), $X_\kappa=\sigma(\{0,\dots,k-1\})$ for some $k\le n$; reason: the sort is nondeterministic; indices are 0-based
--   - encoding: $\|p^*-p\|_\infty<\varepsilon$ → $|p^*_i-p_i|<\varepsilon$ for every $i$; reason: same for $n\ge1$, and for $n=0$ there are no extreme stable sets
--   - encoding: "the" ordered family of extreme stable sets → every `ExtremeChain` (an enumeration of exactly the extreme stable sets with $X$ strictly decreasing and $Y$ strictly increasing); reason: Lemma 3.1 makes the enumeration unique, so quantifying over every one is the paper's claim
--   - encoding: the Sinkhorn limit $(M^*,N^*)$ (the limit of $(M_k,N_k)$, Theorem 2.10) → a hypothesis that $(M_k,N_k)$ (or $N_k$) converges to the given matrices; reason: the paper defines the limit through Theorem 2.10, which the mission states separately; for the actual limit the statements coincide
--   - encoding: $[n]$ with $n=|U|=|V|$ → `Fin n` with any `n : ℕ`; reason: 0-based relabelling; for $n=0$ the statement is trivially true
--   - generalization: stated inside the proof of Theorem 4.3, under its hypothesis "$G$ has no perfect matching" (p.16) → that hypothesis is not assumed; reason: the lemma's proof (p.17) never uses it; with the hypothesis added it is the source's claim
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 4.4, p.17

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL
import Definitions.Def_SinkhornHall_Supplement_Extreme

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 4.4 (a 1/(2n²)-accurate marginal sorts out every X_κ).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 4.4, p.17: "If ‖p* − p‖_∞ < 1/(2n²), then the
output contains X_κ for all κ = 0, 1, 2, …, θ."

Setting of §4 (p.15) and §4.2 (pp.16–17): `A` is a nonnegative `n × n` matrix with no zero row or
column, `(r, c) = (1, 1)`, `p* = N*1` for the limit `N*` of the Sinkhorn sequence (2.6),
`X_0 ⊔ Y_0, …, X_θ ⊔ Y_θ` are the extreme stable sets ordered as on p.12, and "the output" is
`U_k = {i_1, …, i_k}` (`k = 0, …, n`) for a sort `p_{i_1} ≤ ⋯ ≤ p_{i_n}` (steps 2–3 of
"Sinkhorn & Sorting Marginals", p.16).

**Formalization Note.** The paper's `p` is `A1` at step 2; the proof uses only the accuracy
hypothesis, and the statement is made for every vector `p ∈ ℝⁿ`. The conclusion holds for every
tie-break `σ` of the sort (`p ∘ σ` monotone) and every ordering of the extreme stable sets
(`ExtremeChain`). `‖p* − p‖_∞ < ε` is written coordinatewise. `N*` enters as a hypothesis
`N_k → N*` (Theorem 2.10). -/
theorem lemma_4_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j)
    (Nstar : Matrix (Fin n) (Fin n) ℝ) (hN : Tendsto (sinkhornN A 1 1) atTop (𝓝 Nstar))
    (p : Fin n → ℝ) (hp : ∀ i, |(∑ j, Nstar i j) - p i| < 1 / (2 * (n : ℝ) ^ 2))
    (σ : Equiv.Perm (Fin n)) (hσ : Monotone (p ∘ σ)) (ch : ExtremeChain A 1 1) :
    ∀ k : Fin (ch.θ + 1), ∃ m ≤ n, ch.X k = sortPrefix σ m := by sorry

end SinkhornHall.Supplement
