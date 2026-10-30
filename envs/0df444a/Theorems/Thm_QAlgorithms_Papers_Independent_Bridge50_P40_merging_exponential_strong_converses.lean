-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_merging_exponential_strong_converses
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.merging_exponential_strong_converses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:54:56.145219+00:00
-- url     : https://prove2.me/theorems/9b5e1ecf-becc-4919-b6f0-03121cf9ad51
-- title:
--   Both exponential strong converses for quantum state merging
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\psi^{ABR}$ be one fixed normalized pure source, with Alice holding $A$, Bob holding $B$, and inaccessible reference $R$. An $n$-copy merging protocol starts with $\psi^{\otimes n}\otimes\Phi_K$ and targets $\Phi_L\otimes\psi^{\otimes n}$, with both source shares at Bob and the same reference retained. Here $n\ge1$ and $K,L\ge1$ are arbitrary integer Schmidt ranks. Let $f(P)$ be the actual complete-output root fidelity and $0\le F\le1$ any lower bound on $f(P)$. All source entropies below are single-copy entropies.
--
--   Fix real ceilings $r_e<S(A|B)_\psi$ and $r_c<I(A:R)_\psi$, where $S(A|B)=S(AB)-S(B)$ and $I(A:R)=S(A)+S(R)-S(AR)$. There exist $1<a_e\le2$, $\tfrac12<a_c<1$ and constants $c_e,c_c>0$, chosen before every block length and protocol, such that
--
--   $$
--   \begin{aligned}
--   c_e&=\frac{a_e-1}{2a_e}\big[S_{1/(2-a_e)}(AB)-S_{2-a_e}(B)-r_e\big],\\
--   c_c&=\frac{1-a_c}{4a_c}\big[S_{b_c}(A)+S_{b_c}(R)-S_{a_c}(AR)-r_c\big],\qquad b_c=\frac{a_c}{2a_c-1},\\
--   f(P)&\le2^{-c_en}\quad\text{for every LOCC merging protocol with }\frac{\log_2K-\log_2L}{n}\le r_e,\\
--   f(P)&\le2^{-c_cn}\quad\text{for every one-way merging protocol with }\frac{\log_2|X|}{n}\le r_c.
--   \end{aligned}
--   $$
--
--   The first entropy in $c_e$ is $S_\infty(AB)$ when $a_e=2$. These are uniform exponential bounds below fixed rate ceilings, rather than decay inferred from a rate gap that may vanish with $n$.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 1, Abstract; section 2; Theorems 8 and 9

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P40

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P40

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Information100.P22 (bell)

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply marginalAR)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (cq)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,4,8--10: both advertised exponential merging converses, with
uniform rate ceilings strictly below S(A|B) and I(A:R). Orders and positive
exponents are chosen after the fixed source and ceilings, before all n and all
protocols, including their entanglement ranks and message alphabets. -/
theorem merging_exponential_strong_converses {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (entRate commRate : ℝ)
    (he : entRate < vnEntropy (traceLeft (pureDensity psi)) -
      vnEntropy (traceLeft (traceLeft (pureDensity psi))))
    (hc : commRate < vnEntropy (traceRight (traceLeft (pureDensity psi))) +
      vnEntropy (traceRight (pureDensity psi)) - vnEntropy (marginalAR (pureDensity psi))) :
    ∃ ae ce ac cc : ℝ,
      1 < ae ∧ ae ≤ 2 ∧ (1 : ℝ) / 2 < ac ∧ ac < 1 ∧ 0 < ce ∧ 0 < cc ∧
      ce = (ae - 1) / (2 * ae) *
        (reciprocalEntropy ae (traceLeft (pureDensity psi)) -
          renyiEntropy (2 - ae) (traceLeft (traceLeft (pureDensity psi))) - entRate) ∧
      cc = (1 - ac) / (4 * ac) *
        (renyiEntropy (ac / (2 * ac - 1)) (traceRight (traceLeft (pureDensity psi))) +
          renyiEntropy (ac / (2 * ac - 1)) (traceRight (pureDensity psi)) -
          renyiEntropy ac (marginalAR (pureDensity psi)) - commRate) ∧
      ∀ n : ℕ, 0 < n →
        (∀ P : RankMergingCode A B n, P.rate ≤ entRate →
          mergingFidelity psi n P.K P.L P.operation ≤ (2 : ℝ) ^ (-ce * (n : ℝ))) ∧
        (∀ P : OneWayMergingCode A B n, P.rate ≤ commRate →
          mergingFidelity psi n P.K P.L P.operation ≤ (2 : ℝ) ^ (-cc * (n : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
