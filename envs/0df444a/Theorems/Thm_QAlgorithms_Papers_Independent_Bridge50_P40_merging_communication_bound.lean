-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P40_merging_communication_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P40.merging_communication_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:59:40.64942+00:00
-- url     : https://prove2.me/theorems/e12a500a-0e16-4754-92b4-d09e8674878c
-- title:
--   Finite-block one-way communication strong converse
-- statement:
--   All registers are finite and nonempty. Density operators have trace one, pure states are normalized, all entropies and logarithms are in base two, and $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$ denotes root fidelity. Write $S_a$ for Petz Rényi entropy, with support projection at order zero and the von Neumann limit at order one; $S_\infty(\rho)=-\log_2\lambda_{\max}(\rho)$.
--
--   Let $\psi^{ABR}$ be one fixed normalized pure source, with Alice holding $A$, Bob holding $B$, and inaccessible reference $R$. An $n$-copy merging protocol starts with $\psi^{\otimes n}\otimes\Phi_K$ and targets $\Phi_L\otimes\psi^{\otimes n}$, with both source shares at Bob and the same reference retained. Here $n\ge1$ and $K,L\ge1$ are arbitrary integer Schmidt ranks. Let $f(P)$ be the actual complete-output root fidelity and $0\le F\le1$ any lower bound on $f(P)$. All source entropies below are single-copy entropies.
--
--   Restrict to one-way Alice-to-Bob protocols: Alice applies a CP instrument with finite nonempty classical outcome alphabet $X$, and Bob applies a CPTP channel conditioned on that same outcome. Alice's private Kraus environment is not communicated or charged. For $\tfrac12<a<1$ and $b=a/(2a-1)$,
--
--   $$
--   F\le2^{\frac{n(1-a)}{4a}\left[\frac{\log_2|X|}{n}-S_b(A)_\psi-S_b(R)_\psi+S_a(AR)_\psi\right]}.
--   $$
--
--   The coefficient multiplies the entire bracket. The bound is independent of the supplied and returned entanglement ranks and includes $F=0$.
-- source:
--   A strong converse for the quantum state merging protocol, arXiv:1404.5940v1, PDF p. 9, Theorem 9, equation (45)

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

/-- PDF pp.9--10, Theorem 9, (45): the entire bracket has coefficient
n(1-a)/(4a), with 1/2<a<1. The one-way hypothesis comes from section 4.2.
The proof invokes Lemma 15 beyond its printed range when beta>2; the explicit
statement is retained and this proof gap is recorded in MODERATION_NOTES.md. -/
theorem merging_communication_bound {A B R : Type}
    [Fintype A] [Fintype B] [Fintype R] [Nonempty A] [Nonempty B] [Nonempty R]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi)
    (n : ℕ) (hn : 0 < n) (P : OneWayMergingCode A B n)
    (F a : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hF : F ≤ mergingFidelity psi n P.K P.L P.operation)
    (ha : (1 : ℝ) / 2 < a) (ha1 : a < 1) :
    let beta := a / (2 * a - 1)
    F ≤ (2 : ℝ) ^ ((n : ℝ) * (1 - a) / (4 * a) *
      (P.rate - renyiEntropy beta (traceRight (traceLeft (pureDensity psi))) -
        renyiEntropy beta (traceRight (pureDensity psi)) + renyiEntropy a (marginalAR (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P40

end
