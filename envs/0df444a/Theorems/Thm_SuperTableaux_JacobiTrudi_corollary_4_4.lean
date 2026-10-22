-- Prove2me | Theorems.Thm_SuperTableaux_JacobiTrudi_corollary_4_4
-- name    : SuperTableaux.JacobiTrudi.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:42.438077+00:00
-- url     : https://prove2.me/theorems/c5c5e734-7067-4377-bd53-9cdefb0af3eb
-- title:
--   Corollary 4.4, p. 23 — weight-preserving bijection $\prod_i SST_{\mathcal A/\mathcal B}(\nu_i)\cong\bigsqcup_\mu SST_{\mathcal A/\mathcal B}(\mu)\times SST_{[n]}(\mu)_\nu$
-- statement:
--   Let $\mathcal A,\mathcal B$ be linearly ordered, at most countable, $\mathbb Z_2$-graded sets, $n\ge1$, and $\nu=(\nu_1,\dots,\nu_n)\in\mathbb Z^n$ with $SST_{\mathcal A/\mathcal B}(\nu_i)\neq\emptyset$ for every $i$. Then there is a bijection
--   $$\kappa_{\mathcal A/\mathcal B}:\ SST_{\mathcal A/\mathcal B}(\nu_1)\times\cdots\times SST_{\mathcal A/\mathcal B}(\nu_n)\longrightarrow\bigsqcup_{\mu\in\mathbb Z^n_+}SST_{\mathcal A/\mathcal B}(\mu)\times SST_{[n]}(\mu)_\nu,$$
--   where $SST_{[n]}(\mu)_\nu$ is the set of rational $[n]$-semistandard tableaux of shape $\mu$ with content $\nu$, such that if $\kappa(w)=(P_w,Q_w)$ then
--   $$\mathrm{wt}_{\mathcal A/\mathcal B}(P_w)=\sum_{i=1}^n\mathrm{wt}_{\mathcal A/\mathcal B}(w_i).$$
--   Here $\mathrm{wt}_{\mathcal A/\mathcal B}(T^+,T^-)=\mathrm{wt}_{\mathcal A}(T^+)-\mathrm{wt}_{\mathcal B}(T^-)$.
--
--   This is the RSK-type correspondence of Theorem 4.1 restricted to a fixed content; taking characters it expresses $H^{\mathcal A/\mathcal B}_\nu$ as a combination of the $S^{\mathcal A/\mathcal B}_\mu$ with Kostka coefficients.
--
--   **Formalization Note** The union runs over all $\mu\in\mathbb Z^n_+$; the summands with $SST_{\mathcal A/\mathcal B}(\mu)=\emptyset$ (i.e. $\mu\notin\mathscr P_{\mathcal A/\mathcal B,n}$) are empty, so this is the paper's union over $\mathscr P_{\mathcal A/\mathcal B,n}$. The statement asserts the existence of a bijection with the weight property instead of naming the insertion map $\kappa_{\mathcal A/\mathcal B}$; the weight property is Corollary 4.3 ($\mathrm{wt}_{\mathcal A/\mathcal B}(w)=\mathrm{wt}_{\mathcal A/\mathcal B}(P_w)$), which the paper's "also gives" carries over. A bijection without it would only compare cardinalities of countable sets. The A/B-weight is stored as one exponent vector on $\mathcal A\sqcup\mathcal B$ (the $\mathcal B$ part counts letters of $T^-$, i.e. exponents of the $x_b^{-1}$).
-- source:
--   Kwon, Rational semistandard tableaux and character formula for the Lie superalgebra ĝl∞|∞, arXiv:math/0605005v1, pp. 22–23, Corollary 4.4 with the weight property of Corollary 4.3

import Mathlib
import Definitions.Def_SuperTableaux_JacobiTrudi_Setting

namespace SuperTableaux.JacobiTrudi
theorem corollary_4_4 {A B : Type*} [LinearOrder A] [Countable A] [LinearOrder B] [Countable B]
    (oddA : A → Bool) (oddB : B → Bool) (n : ℕ) (hn : 0 < n) (nu : Fin n → ℤ)
    (hnu : ∀ i, Nonempty (ABTab oddA oddB (level1 (nu i)))) :
    ∃ e : ((i : Fin n) → ABTab oddA oddB (level1 (nu i))) ≃
        (Σ mu : GenPartition n, ABTab oddA oddB mu × {T : RatTab n mu // content T = nu}),
      ∀ w, wtAB (e w).2.1 = ∑ i, wtAB (w i) := by sorry
end SuperTableaux.JacobiTrudi
