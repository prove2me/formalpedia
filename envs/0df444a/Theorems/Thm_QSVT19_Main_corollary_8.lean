-- Prove2me | Theorems.Thm_QSVT19_Main_corollary_8
-- name    : QSVT19.Main.corollary_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:40.245821+00:00
-- url     : https://prove2.me/theorems/a827f9e7-c554-4e49-817a-c9097249ec5e
-- title:
--   Corollary 8: quantum signal processing using reflections
-- statement:
--   Let $d\ge1$ and let $P\in\mathbb C[x]$ have degree $d$, parity $d\bmod2$, $|P(x)|\le1$ on $[-1,1]$, $|P(x)|\ge1$ for $|x|\ge1$, and, if $d$ is even, $P(ix)P^*(ix)\ge1$ for all real $x$. Then there is $\Phi=(\varphi_1,\dots,\varphi_d)\in\mathbb R^d$ such that for every $x\in[-1,1]$
--   $$\prod_{j=1}^d\bigl(e^{i\varphi_j\sigma_z}R(x)\bigr)=\begin{pmatrix}P(x)&\cdot\\ \cdot&\cdot\end{pmatrix},\qquad R(x)=\begin{pmatrix}x&\sqrt{1-x^2}\\ \sqrt{1-x^2}&-x\end{pmatrix}.$$
--   Moreover, for this $\Phi$, $P(x)=x^d\prod_{j=1}^d e^{i\varphi_j}$ for $x\in\{-1,1\}$, and, if $d$ is even, $P(0)=e^{-i\sum_{j=1}^d(-1)^j\varphi_j}$.
--
--   This converts the $W(x)$-based characterization of quantum signal processing into the reflection form used for singular value transformation.
--
--   **Formalization Note** The hypothesis $d\ge1$ is added: at $d=0$ the constant $P\equiv e^{i\alpha}$, $\alpha\notin2\pi\mathbb Z$, meets every condition but the empty product is $I$; the paper's proof says "for some $d\ge1$". Phases are 0-based, so $(-1)^j$ becomes $(-1)^{j+1}$.
-- source:
--   Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, p. 12–13, Corollary 8, (14)

import Definitions.Def_QSVT19_Main_Setting

set_option autoImplicit false

open scoped ComplexOrder
open Polynomial Matrix

namespace QSVT19.Main

/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Corollary 8, pp. 12–13: "Let P ∈ C[x] be a degree-d polynomial, such that
• P has parity-(d mod 2), • ∀x ∈ [−1, 1]: |P(x)| ≤ 1, • ∀x ∈ (−∞, −1] ∪ [1, ∞): |P(x)| ≥ 1,
• if d is even, then ∀x ∈ R: P(ix)P^∗(ix) ≥ 1.
Then there exists Φ ∈ R^d such that ∏_{j=1}^d (e^{iφ_jσ_z}R(x)) = [P(x) .; . .]. (14)
Moreover for x ∈ {−1, 1} we have that P(x) = x^d ∏_{j=1}^d e^{iφ_j}, and for d even
P(0) = e^{−i∑_{j=1}^d(−1)^jφ_j}."

**Formalization Note.** The four bullets and "degree-d" are `Cor8Requirements d P`. (14) is
required for every `x ∈ [−1, 1]`, the domain of `R(x)` (Definition 7); "`[P(x) .; . .]`" says that
the top-left entry is `P(x)`. The "Moreover" values are stated for the same `Φ`. `Φ` is 0-based, so
the paper's `(−1)^j` (with `j = 1, …, d`) is `(−1)^(j+1)` for `j : Fin d`. The hypothesis `1 ≤ d`
is added: at `d = 0` the statement is false (`P ≡ e^{iα}`, `α ∉ 2πℤ`, meets every bullet, while
the empty product is `I`); the proof says "for some d ≥ 1". -/
theorem corollary_8 (d : ℕ) (hd : 1 ≤ d) (P : ℂ[X]) (hP : Cor8Requirements d P) :
    ∃ Φ : Fin d → ℝ, (∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl Φ x 0 0 = P.eval (x : ℂ)) ∧ (∀ x : ℝ, (x = -1 ∨ x = 1) → P.eval (x : ℂ) = (x : ℂ) ^ d * ∏ j : Fin d, Complex.exp (Φ j * Complex.I)) ∧ (Even d → P.eval 0 = Complex.exp (-(∑ j : Fin d, (-1 : ℂ) ^ (j.val + 1) * (Φ j : ℂ)) * Complex.I)) := by sorry

end QSVT19.Main
