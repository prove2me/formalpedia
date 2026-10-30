-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_all_erasure_patterns
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.all_erasure_patterns
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:55:07.197522+00:00
-- url     : https://prove2.me/theorems/49a850f7-76f4-4e50-a77f-553379dd42e9
-- title:
--   §4.3: simultaneous erasure bounds and flagged mixtures
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension.
--
--   Fix $a\in(0,1)$. Work along admissible integer sequences $n\to\infty$ with $k,t\ge1$ and $\alpha=an$ exactly. The constants below are positive and depend only on $a$, preceding the growth sequence, ancilla, and erased-wire choices; the eventual threshold may depend on the sequence. The displayed little-o ratio tends to zero. Expectations are integrable, and a probability bound allows a zero bad-event probability. For each metric use its own regime: $k^2t^2/n\to0$ for Choi and $kt^2/n\to0$ for worst error. Let $B$ denote the corresponding leading bound multiplied by $1+C$ times its relative remainder. There is one exceptional set of probability at most $e^{-cn}$ outside which every $t$-wire location and every probability mixture of those locations with a classical location flag has error at most $B$. Every fixed flagged mixture also has integrable mean error at most $B$ eventually. More explicitly, for any real threshold $B$ and nonnegative $p$ bounding each site's failure probability,
--
--   $$\Pr[\exists S,\ |S|=t:\varepsilon_S>B]\le\binom nt p.$$
--
--   For $t/n\to0$ with $t\le n$ and $n\to\infty$, $\log_2\binom nt/n\to0$. Thus the union bound preserves exponential concentration. A fixed encoder need not have equal errors at different sites.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 12, §4.3: simultaneous erasure bounds and flagged mixtures

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Section 4.3, PDF p.12: simultaneous sites and flagged mixtures. The finite
union bound retains binomial(n,t), and t=o(n) gives subexponential amplification. -/
theorem all_erasure_patterns :
    PatternGuarantee ChargeHaar ∧
    (∀ n k alpha t : ℕ, ∀ A : Ancilla n k alpha, ∀ worst : Bool,
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ)), ChargeHaar n mu → ∀ B p : ℝ, 0 ≤ p →
      (∀ S : Finset (Fin n), S.card = t →
        mu {U | B < siteError worst A S U} ≤ ENNReal.ofReal p) →
      mu {U | ∃ S : Finset (Fin n), S.card = t ∧ B < siteError worst A S U} ≤
        ENNReal.ofReal ((n.choose t : ℝ) * p)) ∧
    (∀ n t : ℕ → ℕ, Tendsto n atTop atTop → (∀ i, t i ≤ n i) →
      Tendsto (fun i => (t i : ℝ)/n i) atTop (nhds 0) →
      Tendsto (fun i => Real.logb 2 (Nat.choose (n i) (t i)) / n i) atTop (nhds 0)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
