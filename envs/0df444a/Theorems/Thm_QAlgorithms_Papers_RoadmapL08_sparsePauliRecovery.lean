-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL08_sparsePauliRecovery
-- name    : QAlgorithms.Papers.RoadmapL08.sparsePauliRecovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:35:22.564974+00:00
-- url     : https://prove2.me/theorems/eb4c5b3f-ae99-44b7-80f4-36b990e7f4d8
-- title:
--   Recovery of sparse Pauli error rates from noisy eigenvalues
-- statement:
--   Fix a sparsity exponent $0<\delta<1/2$. There are positive constants $C,c,\beta$ and a threshold $n_0\ge1$, depending only on this fixed exponent and public design/code choices, and a public construction of the subsampling and peeling protocol for every $n\ge n_0$ and integer $s=4^{\delta n}$.
--
--   The labels of the $N=4^n$ phase-free $n$-qubit Paulis are $a=(a_x,a_z)\in\mathbb F_2^{2n}$. Let $K$ be uniform among the size-$s$ subsets of these labels. For each possible $K$, assign arbitrary nonnegative rates $p^{(K)}$ with total mass one, support exactly $K$, and $p^{(K)}_a\ge\epsilon_0>0$ on $K$. This assignment is independent of the protocol's public randomness and observation noise. The associated channel is $\mathcal E(\rho)=\sum_a p_aP_a\rho P_a$, and its eigenvalues are
--   $$
--   \lambda_a=\sum_b(-1)^{a_x\cdot b_z+a_z\cdot b_x}p_b.
--   $$
--   The observed eigenvalue vector has independent centered Gaussian errors of variance $\xi^2$, with $\xi\ge0$, independent of the support and the public design. Repeated reads use the same indexed observation and are counted as queries.
--
--   The construction chooses $B=2^b$ bins with $s\le B\le Cs$, constantly many subsampling groups, and $P_1,P_2=\Theta(n)$ offsets. Random offsets and binary hash matrices are sampled independently and uniformly before the hidden input. Coded offsets use a full-rank binary linear code with positive constant relative distance and a public, query-free, linear-time decoder. The decoder's realization, correction property and time bound are conclusions of the construction. Assume
--   $$
--   \xi^2\le\min\!\left(\frac{B}{s^2},1\right),
--   \qquad
--   \epsilon_0\ge\frac{2\xi}{\sqrt B}.
--   $$
--   Algorithms 2–4 produce a list of distinct labels with support exactly $K$ and estimated rates $\widehat p$, zero off the reported support, satisfying
--   $$
--   \Pr\!\left[
--   \operatorname{supp}(\widehat p)=K
--   \ \text{and}\
--   \|\widehat p-p\|_\infty\le\frac{2\xi}{\sqrt B}
--   \right]\ge1-e^{-cn}.
--   $$
--   The probability averages over the uniform support, public design, Gaussian observations, and any internal decoder randomness. Every execution uses at most $Csn$ eigenvalue reads and $Csn^2$ classical arithmetic/indexing instructions. The computed conditional success probabilities are measurable.
--
--   This result recovers both the locations and values of sparse Pauli errors from noisy eigenvalues. It does not assert a quantum measurement sample complexity.
--
--   **Formalization Note** The frozen, independently reviewed program composition is used directly. It separates the ordinary $b$-bit WHT from the symplectic $2n$-bit label pairing, resolves the printed dimensional inconsistencies as approved in the definition review, and retires peeled bins according to the graph description. The theorem does not assume successful bin detection, favorable graph events, accuracy, runtime, or independence of overlapping bin errors.
-- source:
--   Fast Estimation of Sparse Quantum Noise, arXiv:2007.07901v2, Theorem 1; Assumptions 1, Algorithms 2–4, PDF p. 8. https://arxiv.org/abs/2007.07901v2 . PDF SHA-256: 0e91fc6b0f2e2c3bb9e12a9535b4619529fd95253e267b54f968df939dae438b.

import Definitions.Def_QAlgorithms_Defs_SparsePauliNoiseAlgorithms
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapL08

open QAlgorithms.SparsePauliNoise

/-- Harper, Yu and Flammia, arXiv:2007.07901v2, Theorem 1 (PDF pp.8,15),
with Assumptions 1 (p.7), Definition 1 (pp.12,15), and Algorithms 2--4.
The public construction precedes the unknown support/rates and Gaussian observations.
The named program is subsampling followed by peeling with its actual bin detector.
Probability averages over exact-size random support and independent public design/noise.

Source interpretation independently approved in wave7/defs/MODERATION-r2.md:
Algorithm 2's dimensionally inconsistent J_b is replaced by the separate ordinary b-bit
WHT and query addresses J_n M_c l+d; offsets have length 2n, as Eq.(13) requires.
Peeled source bins are retired, as the graph description on pp.13,18 requires.
Algorithm 3's return is after BOTH loops on the rendered p.14 (contrary to the plan note).
The claim retains 2*xi/sqrt(B), exact support recovery, and exponential failure.
No favorable graph, successful prior detection, independence of bin noise, accuracy,
or runtime is assumed. Concrete code/decoder synthesis is existential, not supplied
as a hypothesis. Classical work is the frozen arithmetic/indexing instruction count. -/
theorem sparsePauliRecovery :
    ∀ delta : ℝ, 0 < delta → delta < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ beta : ℝ, 0 < beta ∧
    ∃ n0 : ℕ, 1 ≤ n0 ∧
    ∃ construct : (n : {n : ℕ // n0 ≤ n}) → (s : ℕ) → RecoveryDesign n.val,
    ∀ n s : ℕ, ∀ (hn : n0 ≤ n) (hs : 1 < s)
      (hfeasible : s ≤ Fintype.card (Label n)),
    (s : ℝ) = (4 : ℝ) ^ (delta * n) →
    let D := construct ⟨n, hn⟩ s
    let B := 2 ^ D.b
    (s : ℝ) ≤ B ∧ (B : ℝ) ≤ C * s ∧
    (D.groups : ℝ) ≤ C ∧ n ≤ D.P1 ∧ 2 * n ≤ D.P2 ∧
    ((D.P1 + D.P2 : ℕ) : ℝ) ≤ C * n ∧
    (D.iterations : ℝ) ≤ C * n ∧
    Function.Injective D.code.mulVec ∧
    (∀ message : Fin (n + n) → ZMod 2, message ≠ 0 →
      beta * D.P2 ≤ (hammingNorm (D.code.mulVec message) : ℝ)) ∧
    (∀ word : Fin D.P2 → ZMod 2,
      let memory : ℕ → ℝ := fun i =>
        if hi : i < D.P2 then (if word ⟨i, hi⟩ = 1 then 1 else 0) else 0
      ∀ state ∈ (execution (fun _ => 0) D.decoder ⟨memory, [], [], 0, false⟩).support,
        state.failed = false ∧ (state.work : ℝ) ≤ C * n ∧
        ∀ label : Label n,
          (hammingDist word (D.code.mulVec (Fin.append label.2 label.1)) : ℝ) ≤
              beta * D.P2 →
          ∀ i : Fin (n + n), state.memory (D.P2 + i.val) =
            if Fin.append label.1 label.2 i = 1 then 1 else 0) ∧
    ∀ xi : ℝ, ∀ hxi : 0 ≤ xi, ∀ epsilon0 : ℝ, 0 < epsilon0 →
    xi ^ 2 ≤ min ((B : ℝ) / (s : ℝ) ^ 2) 1 →
    2 * xi / Real.sqrt B ≤ epsilon0 →
    let Seed := (Fin D.groups → Matrix (Fin (n + n)) (Fin D.b) (ZMod 2)) ×
      (Fin D.groups → Fin D.P1 → Label n)
    let design : Seed → RecoveryDesign n := fun seed =>
      { D with hashMatrix := seed.1, randomOffsets := seed.2 }
    let program : Seed → OracleProgram n := fun seed =>
      (subsamplingProgram (design seed)).then (peelingProgram (design seed) xi hxi)
    (∀ seed : Seed, ∀ observations : Label n → ℝ,
      ∀ state ∈ (execution observations (program seed) ⟨0, [], [], 0, false⟩).support,
        (state.trace.length : ℝ) ≤ C * s * n ∧
        (state.work : ℝ) ≤ C * s * n ^ 2) ∧
    ∀ rates : (K : {K : Finset (Label n) // K.card = s}) →
        AdmissibleRates n s K.val epsilon0,
    (∀ K seed, Measurable (fun observations : Label n → ℝ =>
      (execution observations (program seed) ⟨0, [], [], 0, false⟩).toOuterMeasure
        {state | recoveryEvent (design seed) (rates K).rate xi hxi state})) ∧
    (∑ K : {K : Finset (Label n) // K.card = s},
      (supportLaw n s (lt_trans Nat.zero_lt_one hs) hfeasible K) *
        ∑ seed : Seed, (PMF.uniformOfFintype Seed seed) *
          ∫⁻ observations : Label n → ℝ,
            (execution observations (program seed) ⟨0, [], [], 0, false⟩).toOuterMeasure
              {state | recoveryEvent (design seed) (rates K).rate xi hxi state}
            ∂noisyEigenvalueLaw (rates K).rate (rates K).distribution xi hxi) ≥
      ENNReal.ofReal (1 - Real.exp (-c * n)) := by sorry

end QAlgorithms.Papers.RoadmapL08
