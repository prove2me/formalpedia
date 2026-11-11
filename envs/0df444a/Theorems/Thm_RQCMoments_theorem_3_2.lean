-- Prove2me | Theorems.Thm_RQCMoments_theorem_3_2
-- name    : RQCMoments.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:13:23.789551+00:00
-- url     : https://prove2.me/theorems/c6d50d63-e093-43e7-b0aa-00536d8e6090
-- title:
--   Theorem 3.2 — design moments of block probabilities are relatively close to Haar
-- statement:
--   Let $N\ge 2$ and let $\mu$ be an $\varepsilon$-approximate unitary $k$-design on $U(N)$, i.e. a strong $\varepsilon$-approximate $(k,k)$-design with relative error (Remark 2.3). Fix a column index $y$ and a set $S$ of row indices, and let
--   $$
--   X(U)=\sum_{r\in S}|\langle r|U|y\rangle|^2
--   $$
--   be the total probability of the block $S$ (for $S=\{x\}$ this is the single output probability $|\langle x|U|y\rangle|^2$). Then:
--   1. for every polynomial $p$ of degree at most $k$ with complex coefficients,
--   $$
--   (1-\varepsilon)\,\mathbb E_{\mathrm{Haar}(N)}[|p(X)|^2]\le \mathbb E_{\mu}[|p(X)|^2]\le(1+\varepsilon)\,\mathbb E_{\mathrm{Haar}(N)}[|p(X)|^2];
--   $$
--   2. for every two complex polynomials $p,q$ of degree at most $k$,
--   $$
--   \Big|\mathbb E_{\mu}\big[\overline{p(X)}\,q(X)\big]-\mathbb E_{\mathrm{Haar}(N)}\big[\overline{p(X)}\,q(X)\big]\Big|\le\varepsilon\sqrt{\mathbb E_{\mathrm{Haar}(N)}[|p(X)|^2]\cdot\mathbb E_{\mathrm{Haar}(N)}[|q(X)|^2]};
--   $$
--   3. in particular, $\big|\mathbb E_{\mu}[q(X)]-\mathbb E_{\mathrm{Haar}(N)}[q(X)]\big|\le\varepsilon\sqrt{\mathbb E_{\mathrm{Haar}(N)}[|q(X)|^2]}$.
--
--   This is the moment-transfer step of the paper: it is used, through sums of squares, to compare expectations of nonnegative polynomials under the design and under Haar in the proof of Theorem 4.9.
--
--   Differences from the source:
--
--   - encoding: a probability distribution on U(N) → a Borel probability measure on the subtype Matrix.unitaryGroup (Fin N) ℂ (Borel σ-algebra of the subspace topology); reason: Lean representation of a distribution on the compact group U(N); same instances
--   - encoding: column index y and set S of row indices in {0, …, N−1} → y : Fin N and S : Finset (Fin N); reason: 0-based indices; every set of rows of an N-row matrix is finite; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 3.2, (41)–(43), pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_entry

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **Theorem 3.2** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 3.2, pp.18–19, PDF pp.20–21).
For `N ≥ 2` let `μ` be a strong `ε`-approximate `(k,k)`-design on `U(N)` (Remark 2.3). Fix a column
`y` and a set `S` of rows, and let `X(U) = ∑_{r∈S} |⟨r|U|y⟩|²` (41). Then for every complex
polynomial `p` of degree at most `k`:
(42) `(1−ε) E_{Haar}|p(X)|² ≤ E_μ|p(X)|² ≤ (1+ε) E_{Haar}|p(X)|²`;
(43) for all complex `p, q` of degree at most `k`,
`|E_μ[conj(p(X)) q(X)] − E_{Haar}[conj(p(X)) q(X)]| ≤ ε √(E_{Haar}|p(X)|² · E_{Haar}|q(X)|²)`;
and in particular (`p ≡ 1`) `|E_μ[q(X)] − E_{Haar}[q(X)]| ≤ ε √(E_{Haar}|q(X)|²)`.

**Formalization Note** "Degree at most `k`" is `natDegree ≤ k` (the zero polynomial is allowed);
`X(U)` is real and is evaluated in `p` as a complex number. -/
theorem theorem_3_2 {N : ℕ} (hN : 2 ≤ N) (k : ℕ) (ε : ℝ) (μ : Measure (Matrix.unitaryGroup (Fin N) ℂ))
    (hμ : IsStrongDesign μ k k ε) (y : Fin N) (S : Finset (Fin N)) :
    let Xb : Matrix.unitaryGroup (Fin N) ℂ → ℂ := fun U => ((∑ r ∈ S, entry r y U : ℝ) : ℂ)
    (∀ P : Polynomial ℂ, P.natDegree ≤ k →
      (1 - ε) * ∫ U, Complex.normSq (P.eval (Xb U)) ∂(QAlgorithms.Schur.unitaryHaar N) ≤
          ∫ U, Complex.normSq (P.eval (Xb U)) ∂μ ∧
        ∫ U, Complex.normSq (P.eval (Xb U)) ∂μ ≤
          (1 + ε) * ∫ U, Complex.normSq (P.eval (Xb U)) ∂(QAlgorithms.Schur.unitaryHaar N)) ∧
    (∀ P Q : Polynomial ℂ, P.natDegree ≤ k → Q.natDegree ≤ k →
      ‖(∫ U, star (P.eval (Xb U)) * Q.eval (Xb U) ∂μ) -
          ∫ U, star (P.eval (Xb U)) * Q.eval (Xb U) ∂(QAlgorithms.Schur.unitaryHaar N)‖ ≤
        ε * Real.sqrt ((∫ U, Complex.normSq (P.eval (Xb U)) ∂(QAlgorithms.Schur.unitaryHaar N)) *
          ∫ U, Complex.normSq (Q.eval (Xb U)) ∂(QAlgorithms.Schur.unitaryHaar N))) ∧
    (∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ‖(∫ U, Q.eval (Xb U) ∂μ) - ∫ U, Q.eval (Xb U) ∂(QAlgorithms.Schur.unitaryHaar N)‖ ≤
        ε * Real.sqrt (∫ U, Complex.normSq (Q.eval (Xb U)) ∂(QAlgorithms.Schur.unitaryHaar N))) := by sorry

end RQCMoments
