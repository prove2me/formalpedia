-- Prove2me | Theorems.Thm_RSCapacity_lemma_6_6
-- name    : RSCapacity.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:48.875575+00:00
-- url     : https://prove2.me/theorems/74768cf1-a542-4e03-ba18-a27ff50ee009
-- title:
--   Lemma 6.6 (Triangular coefficient equation)
-- statement:
--   Let $F$ be algebraically closed of characteristic $p$, let $d<p$, and let $Q\in F[Z,X,Y_0,\dots,Y_r]$ depend on $Y_s$ but on no $Y_j$ with $j>s$. Fix $\alpha\in F$, write $P(\alpha+U)=\sum_{j=0}^dc_jU^j$ with indeterminates $c_j$, let $H_\alpha(Z,c_0,\dots,c_s)=\frac{\partial Q}{\partial Y_s}(Z,\alpha,c_0,\dots,c_s)$ and let $F_{\alpha,t}$ be the coefficient of $U^t$ in $Q(Z,\alpha+U,P(\alpha+U),P^{[1]}(\alpha+U),\dots,P^{[s]}(\alpha+U))$. For $1\le t\le d-s$,
--   $$F_{\alpha,t}=\binom{s+t}{s}H_\alpha(Z,c_0,\dots,c_s)\,c_{s+t}+G_{\alpha,t}(Z,c_0,\dots,c_{s+t-1})$$
--   for a polynomial $G_{\alpha,t}$, and the coefficient $\binom{s+t}{s}$ is nonzero in $F$.
--
--   The equation is linear in the newest Taylor coefficient $c_{s+t}$, so the jet is determined recursively wherever $H_\alpha\neq0$.
--
--   Differences from the source:
--   - encoding: F of characteristic p with d < p → d < ringChar F; reason: characteristic 0 is excluded exactly as on the page
--   - encoding: G_{α,t}(Z, c_0, …, c_{s+t−1}) → a polynomial in F[Z, c_0, …, c_d] whose variables have index at most s + t; reason: the variables Z, c_0, …, c_{s+t−1}
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 6.6, p.26 (PDF 28); setting §6.3, p.25 (PDF 27) and §6.3.1, p.26

import Mathlib
import Definitions.Def_RSCapacity_JetCoefficients

set_option autoImplicit false

namespace RSCapacity

open MvPolynomial

/-- **Lemma 6.6 (Triangular coefficient equation).** Jeronimo, arXiv:2609.05870 (held version of
November 1, 2026, sha256 9a0069bd…), Lemma 6.6, p.26 (PDF 28), in the setting of §6.3, p.25 and
§6.3.1, p.26: F is algebraically closed of characteristic p, d < p, Q ∈ F[Z, X, Y_0, …, Y_r]
depends on Y_s but on no Y_j with j > s, α ∈ F, P(α + U) = ∑_{j=0}^{d} c_j U^j,
H_α(Z, c_0, …, c_s) := ∂Q/∂Y_s (Z, α, c_0, …, c_s) (59), and F_{α,t} is the coefficient of U^t in
Q(Z, α + U, P(α + U), P^{[1]}(α + U), …, P^{[s]}(α + U)) (60). For 1 ≤ t ≤ d − s,
F_{α,t} = C(s+t, s) H_α(Z, c_0, …, c_s) c_{s+t} + G_{α,t}(Z, c_0, …, c_{s+t−1}) (61) for a
polynomial G_{α,t}. In particular, because d < p, the coefficient C(s+t, s) is nonzero in F.

**Formalization Note.** The c_j are indeterminates: F_{α,t}, H_α and G_{α,t} live in
F[Z, c_0, …, c_d] (`MvPolynomial (Fin (d + 2)) F`, Z = variable 0, c_l = variable l + 1), so
"G_{α,t} depends only on Z, c_0, …, c_{s+t−1}" says its variables have index at most s + t.
"Characteristic p with d < p" is `d < ringChar F` (characteristic 0 is excluded, as on the page). -/
theorem lemma_6_6 {F : Type*} [Field F] [IsAlgClosed F] (r d : ℕ) (hd : d < ringChar F)
    (Q : MvPolynomial (Fin (r + 3)) F) (s : Fin (r + 1)) (hs : 0 < Q.degreeOf (yVar3 s))
    (hs' : ∀ j : Fin (r + 1), s < j → Q.degreeOf (yVar3 j) = 0) (α : F) (t : ℕ) (ht : 1 ≤ t)
    (htd : (s : ℕ) + t ≤ d) :
    (∃ G : MvPolynomial (Fin (d + 2)) F, (∀ v ∈ G.vars, (v : ℕ) ≤ (s : ℕ) + t) ∧
      jetCoeff r d α Q t =
        C ((((s : ℕ) + t).choose s : ℕ) : F) * Halpha r d α s Q * cVar d ((s : ℕ) + t) + G) ∧
    ((((s : ℕ) + t).choose s : ℕ) : F) ≠ 0 := by sorry

end RSCapacity
