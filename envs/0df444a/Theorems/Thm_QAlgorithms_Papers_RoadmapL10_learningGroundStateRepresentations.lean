-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL10_learningGroundStateRepresentations
-- name    : QAlgorithms.Papers.RoadmapL10.learningGroundStateRepresentations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:35:00.158348+00:00
-- url     : https://prove2.me/theorems/0f8289e2-4b4d-4267-998f-94e86cde7991
-- title:
--   Learning ground-state representations from one-shot Pauli shadows
-- statement:
--   Fix a finite spatial dimension $d$, bounds on the number and geometric radius of sites in each Hamiltonian term, a local-term density bound $b_d+c_dr^d$, a spectral gap $\gamma>0$, an observable locality bound $q$, and a confidence parameter $\delta\in(0,1)$. Consider $n$-qubit Hamiltonians $H(x)=\sum_j h_j(x)$, smoothly parametrized by $x\in[-1,1]^m$. Each term is Hermitian, obeys $\|h_j(x)\|_\infty\le1$, and has directional derivative of operator norm at most one in every Euclidean unit parameter direction. These properties hold throughout the cube; smoothness at its boundary uses a local smooth extension. Every Hamiltonian has an excited energy and a gap at least $\gamma$ above its entire ground eigenspace. Let $\rho(x)$ be the normalized projector onto that eigenspace, allowing degeneracy.
--
--   For a fixed Hermitian observable $O=\sum_{i=1}^L O_i$, each term supported on at most $q$ qubits (not necessarily neighboring), choose a norm budget $B\ge1$ satisfying $\sum_i\|O_i\|_\infty\le B$. A smaller norm budget may be replaced by one. There are uniform positive constants, depending only on the fixed physical bounds, $q$, and $\delta$, such that for every fixed mean-squared error tolerance $\varepsilon\in(0,1]$ and all sufficiently large $m$, public sample counts, cutoffs, and actual classical arithmetic/RAM programs can be selected before the unknown Hamiltonian family, training draw, observable entries, and test parameter. The training set consists of $N$ independent uniform parameter draws, with one fresh-copy randomized Pauli snapshot $S_\ell$ at each point. Pauli axes are independently uniform; the joint measurement outcomes obey the Born law.
--
--   The named predictor is
--   $$
--   \widehat{\sigma}_N(x)=\frac1N\sum_{\ell=1}^N\kappa_\Lambda(x,x_\ell)S_\ell,\qquad
--   \kappa_\Lambda(x,y)=\sum_{\substack{k\in\mathbb Z^m\\\|k\|_2\le\Lambda}}
--   \cos\!\bigl(\pi k\cdot(x-y)\bigr).
--   $$
--   For each observable fixed before the training draw,
--   $$
--   \Pr_{\mathcal T}\!\left[
--   \mathbb E_{x\sim\mathrm{Unif}[-1,1]^m}
--   \left|\operatorname{tr}\!\left(O\widehat{\sigma}_N(x)\right)
--   -\operatorname{tr}\!\left(O\rho(x)\right)\right|^2
--   \le\varepsilon\right]\ge1-\delta,
--   $$
--   with $N\le C B^2m^{C B^2/\varepsilon}$ and computed classical training and prediction work $O((n+L)B^2m^{O(B^2/\varepsilon)})$. The compact representation stores $mN$ real parameter words and $nN$ six-valued labels, encodable in $3nN$ bits. The programs read and store those data and compute the observable value; they do not materialize the represented matrix. Ground-state preparation and data generation are excluded from this classical work.
--
--   For every fixed subsystem $A$ of at most $q$ qubits, separately with confidence at least $1-\delta$,
--   $$
--   \mathbb E_x\left\|\operatorname{tr}_{A^{\mathrm c}}
--   \bigl(\widehat{\sigma}_N(x)-\rho(x)\bigr)\right\|_1
--   \le\sqrt{4^q\varepsilon}.
--   $$
--   Thus taking $\varepsilon=\eta^2/4^q$ gives the informal constant trace-norm error $\eta$ on a fixed few-body reduced matrix. This conversion uses the finite Pauli expansion and allocates confidence $\delta/4^q$ to its coefficients; it leaves the polynomial-in-$m$, linear-in-$n$ conclusion intact at fixed accuracy and locality.
--
--   This result describes generalization in population average for the source's compact shadow predictor. It asserts neither pointwise error nor simultaneous accuracy on all observables or subsystems, and does not require the predicted representation to be positive or trace one.
--
--   **Formalization Note** Theorem 3 on PDF pp.29–30 explicitly identifies itself as the detailed restatement of Theorem 1. Its Eq. (F3) prints exact ground-state labels, whereas its premise and Eqs. (2), (E3), and (F27) specify shadow labels; the latter determine the model above. This discrepancy and the nonperiodic-boundary gap in Lemma 2 are recorded for independent source moderation, without adding periodicity or a gradient bound as hypotheses.
-- source:
--   Provably efficient machine learning for quantum many-body problems, arXiv:2106.12627v4, Theorem 1; detailed Theorem 3, PDF pp.29–30, PDF p. 4. https://arxiv.org/abs/2106.12627v4 . PDF SHA-256: 29485e88e4b744e13ce160f7e1bb54650d92d6bab22590176d04ebd9c913183f.

import Definitions.Def_QAlgorithms_Defs_DirichletShadowLearning
import Definitions.Def_QAlgorithms_Defs_ShadowLearnerPrograms
import Definitions.Def_QAlgorithms_Papers_RoadmapL10_Model
set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapL10

open GroundStateLearning








/-- Theorem 1 (PDF p.4), detailed Theorem 3 (pp.29–30), F.5 (pp.36–39).
The named predictor is Eqs.(2),(E3),(F27), using one Pauli snapshot per training point.
F3 prints exact state labels instead: the shadow-labelled premise and explicit construction
determine the reading here; independent source moderation is required. No periodic parameter
boundary condition or Theorem-4 gradient conclusion is assumed. Lemma 2 has a boundary gap,
recorded in the unit audit; this declaration preserves the printed headline target.

Physical constants, observable locality and confidence precede uniform resource constants.
The norm budget is normalized to B >= 1 (any smaller budget can be enlarged to 1).
Public programs are chosen before the hidden family, training draw and test parameter.
The representation is the frozen predictor; computed program work counts its compact evaluation.
For each fixed subsystem the mean trace-norm error is at most sqrt(4^q * eps).
Setting eps = eta^2 / 4^q gives the informal error eta, with confidence 1-delta.
No simultaneous-all-observables or simultaneous-all-subsystems guarantee is asserted. -/
theorem learningGroundStateRepresentations
    (spatial locality q : ℕ) (hspatial : 0 < spatial)
    (radius bd cd gap delta : ℝ)
    (hradius : 0 ≤ radius) (hbd : 0 ≤ bd) (hcd : 0 ≤ cd) (hgap : 0 < gap)
    (hdelta : 0 < delta ∧ delta < 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ B eps : ℝ, 1 ≤ B → 0 < eps → eps ≤ 1 →
    ∃ m0 : ℕ, 2 ≤ m0 ∧ ∀ n m : ℕ, 0 < n → m0 ≤ m →
    ∃ N : ℕ, ∃ hN : 0 < N, ∃ Lambda : ℝ, ∃ hLambda : 0 ≤ Lambda,
    ∃ load : LearnerProgram,
    ∃ evaluate : (L : ℕ) → (arity : Fin L → ℕ) →
      ((i : Fin L) → Fin (arity i) ↪ Fin n) → LearnerProgram × ℕ,
    (N : ℝ) ≤ C * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
    (∀ data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n,
      let trained := loadedTraining load data
      trained.failed = false ∧ trained.stored.card ≤ (n + m) * N ∧
      (trained.work : ℝ) ≤ C * ((n + m) * N : ℕ) ∧
      (trained.work : ℝ) ≤ C * (n + 1) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
      (∀ l : Fin N, ∀ j : Fin m, trained.memory (l.val * m + j.val) = (data l).1 j) ∧
      ∀ l : Fin N, ∀ j : Fin n,
        trained.memory (m * N + l.val * n + j.val) =
          (shadowLabelCode ((data l).2 j)).val) ∧
    (∀ (L : ℕ) (arity : Fin L → ℕ) (wires : (i : Fin L) → Fin (arity i) ↪ Fin n),
      (∀ i, arity i ≤ q) →
      ∀ localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ,
      (∀ i, (localOp i).IsHermitian) → (∑ i, specNorm (localOp i)) ≤ B →
      ∀ data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n,
      ∀ x : EuclideanSpace ℝ (Fin m), x ∈ parameterCube m →
        let result := evaluatedPrediction load (evaluate L arity wires).1 data x arity localOp
        result.failed = false ∧
        result.memory (evaluate L arity wires).2 =
          ((∑ i, embedOp (localOp i) (wires i)) * predictor hN Lambda hLambda data x).trace.re ∧
        (result.work : ℝ) ≤ C * (n + L) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps) ∧
        (result.stored.card : ℝ) ≤
          C * (n + m + L) * B ^ 2 * (m : ℝ) ^ (C * B ^ 2 / eps)) ∧
    ∀ (terms : ℕ) (H : HamiltonianFamily n m terms spatial),
      H.geometry.cardinalityBound ≤ locality → H.geometry.radiusBound ≤ radius →
      H.geometry.bd ≤ bd → H.geometry.cd ≤ cd →
      (∀ j x, x ∈ parameterCube m → ContDiffAt ℝ ⊤ (H.term j) x) →
      (∀ x ∈ parameterCube m, HasExcitationGap (H.hamiltonian x) gap) →
      ∃ measurable : Measurable (targetGroundFamily H),
      ∃ states : ∀ x ∈ parameterCube m, IsDensityMatrix (targetGroundFamily H x),
      (∀ (L : ℕ) (arity : Fin L → ℕ) (wires : (i : Fin L) → Fin (arity i) ↪ Fin n),
        (∀ i, arity i ≤ q) →
        ∀ localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ,
        (∀ i, (localOp i).IsHermitian) → (∑ i, specNorm (localOp i)) ≤ B →
        trainingLaw (targetGroundFamily H) measurable states N
          {data | (∫⁻ x, ENNReal.ofReal
            (((∑ i, embedOp (localOp i) (wires i)) *
              (predictor hN Lambda hLambda data x - targetGroundFamily H x)).trace.re ^ 2)
              ∂parameterCubeLaw m) ≤ ENNReal.ofReal eps} ≥ ENNReal.ofReal (1 - delta)) ∧
      ∀ (r : ℕ) (w : Fin r ↪ Fin n), r ≤ q →
        trainingLaw (targetGroundFamily H) measurable states N
          {data | (∫⁻ x, ENNReal.ofReal
            (traceNorm (reducedOperator w
              (predictor hN Lambda hLambda data x - targetGroundFamily H x)))
              ∂parameterCubeLaw m) ≤
                ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ q * eps))} ≥
          ENNReal.ofReal (1 - delta) := by sorry

end QAlgorithms.Papers.RoadmapL10
