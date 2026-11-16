-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_theorem_5_4
-- name    : QuantumStateIdentity321.Schur.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:01:42.210577+00:00
-- url     : https://prove2.me/theorems/8e3292f9-1756-4242-a066-e82df3e211ab
-- title:
--   Theorem 5.4 — total variation bound for one binomial coordinate replaced at a uniformly random position
-- statement:
--   Let $p\in(0,1)$, $n\ge1$ and $m\ge0$. Let $X_1,\dots,X_n,Y$ be independent with $X_i\sim\mathrm{Binomial}(m,p)$ and $Y\sim\mathrm{Binomial}(m,1-p)$, let $I$ be uniform on $[n]$ and independent of them, and let $(Z_1,\dots,Z_n)$ equal $(X_1,\dots,X_n)$ except that $Z_I$ is replaced by $Y$. Then
--
--   $$
--   \bigl\|(X_1,\dots,X_n)-(Z_1,\dots,Z_n)\bigr\|_{TV}\le\left(\frac1{4n}\left[\left(\frac{3p^2-3p+1}{p(1-p)}\right)^m-1\right]\right)^{1/2}.
--   $$
--
--   By Lemma 5.3 these two laws are the diagonals of the phase-averaged yes and no states of Problem 1, so this bound gives the $n$-dependent half of the lower bound (Corollary 5.5, Theorem 5.6).
--
--   **Formalization Note** The law of $(Z_1,\dots,Z_n)$ is the mixture $\frac1n\sum_iQ_i$, $Q_i$ being the law with coordinate $i$ replaced; $\|P-Q\|_{TV}=\frac12\sum_x|P(x)-Q(x)|$.
--
--   Differences from the source:
--   - generalization: n ≥ 2 (standing assumption of the paper) → n ≥ 1; reason: the probabilistic statement needs only a nonempty [n] for the uniform I; it specializes to every n ≥ 2
--   - encoding: random variables and their joint law → probability mass functions on Fin n → Fin (m+1); Q = (1/n) Σᵢ Qᵢ; reason: Lean convention; same laws
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Theorem 5.4, PDF/printed p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Supplement_LowerBound

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix

/-- Theorem 5.4, p.20: let `p ∈ (0, 1)`, `X₁, …, Xₙ ∼ Binomial(m, p)` and `Y ∼ Binomial(m, 1 − p)`
independent, `I` uniform on `[n]` and independent of them, and `(Z₁, …, Zₙ)` equal to
`(X₁, …, Xₙ)` with `Z_I` replaced by `Y`. Then
`‖(X₁, …, Xₙ) − (Z₁, …, Zₙ)‖_TV ≤ ((1/(4n)) [((3p² − 3p + 1)/(p(1 − p)))^m − 1])^{1/2}`. -/
theorem theorem_5_4 (n m : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    tvDist (yesLaw n m p) (noLaw n m p) ≤
      Real.sqrt (1 / (4 * (n : ℝ)) *
        (((3 * p ^ 2 - 3 * p + 1) / (p * (1 - p))) ^ m - 1)) := by sorry

end QuantumStateIdentity321.Schur.Supplement
