-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P22_amplitudeDampingPurifies
-- name    : QAlgorithms.Papers.Independent.Frontier30.P22.amplitudeDampingPurifies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:25:27.509979+00:00
-- url     : https://prove2.me/theorems/dda804bf-19bf-4a84-bd6b-ac1f1878eec4
-- title:
--   Amplitude damping approaches vacuum and can increase purity
-- statement:
--   Let $\Phi_t$ be the single-mode bosonic amplitude-damping evolution on the full Fock space, with zero Hamiltonian and jump $F=a$ in the normalization $\mathcal L(X)=aXa^\dagger-\{a^\dagger a,X\}/2$. It is represented by the accepted attenuator Kraus family at amplitude transmissivity $e^{-t/2}$. On number dyads its generator is
--   $$
--   G(|m\rangle\langle n|)=\sqrt{mn}\,|m-1\rangle\langle n-1|-\frac{m+n}{2}|m\rangle\langle n|,
--   $$
--   where the first term is zero when $m=0$ or $n=0$. The corresponding right derivative is in trace norm. The formal commutator form satisfies $\mathcal L(I)=[a,a^\dagger]=I$. All forward-time Kraus sums exist in trace norm and the maps preserve density operators. The vacuum $P_0=|0\rangle\langle0|$ is stationary and pure. For every trace-class density $\rho$,
--   $$
--   \lim_{t\to\infty}\|\Phi_t(\rho)-P_0\|_1=0.
--   $$
--   There also exist a mixed density $\rho$ and times $0\le s<t$ such that $p(\Phi_s(\rho))<p(\Phi_t(\rho))$.
--
--   This exhibits failure of universal purity decrease without asserting a positive derivative for every input or every time. No finite-energy restriction is imposed.
-- source:
--   Conditions for strictly purity-decreasing quantum Markovian dynamics, arXiv:quant-ph/0411119v2, PDF p. 3, Section IV, amplitude-damping example

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P22

local notation "FD" => QAlgorithms.Papers.Independent.Dependency50.P16.LindbladData

local notation "finiteG" => QAlgorithms.Papers.Independent.Dependency50.P16.gkslGenerator

local notation "finiteEvolution" => QAlgorithms.Papers.Independent.Dependency50.P16.semigroupEvolution

local notation "Fock" => QAlgorithms.Papers.Independent.Dependency50.P39.Fock

local notation "BOp" => QAlgorithms.Papers.Independent.Dependency50.P39.FockOperator

local notation "fockKet" => QAlgorithms.Papers.Independent.Dependency50.P39.fockKet

local notation "fockDyad" => QAlgorithms.Papers.Independent.Dependency50.P39.fockDyad

local notation "IsDensity" => QAlgorithms.Papers.Independent.Dependency50.P39.IsDensity

local notation "IsTraceClass" => QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass

local notation "TraceHasSum" => QAlgorithms.Papers.Independent.Dependency50.P39.TraceHasSum

local notation "traceNorm" => QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm

local notation "krausTerm" => QAlgorithms.Papers.Independent.Dependency50.P39.krausTerm

local notation "attenuatorKraus" => QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorKraus

/-- Section IV, PDF p.3: full bosonic amplitude damping has formal L(I)=+I,
is not purity-decreasing for all states, and tends to the pure vacuum.
The limit is in trace norm for every trace-class density, with no energy bound.
Vacuum is stationary; the increase assertion is existential, not universal.
The core derivative fixes the exact rate in Eqs.(2),(4), rather than a rescaled
or finite-dimensional attenuation model. -/
theorem amplitudeDampingPurifies :
    (∀ v : Fock, dampingIdentityForm v = ‖v‖ ^ 2) ∧
    (∀ t : ℝ, 0 ≤ t →
      QAlgorithms.Papers.Independent.Dependency50.P39.AttenuatorRealized
        (Real.exp (-t / 2)) ∧
      QAlgorithms.Papers.Independent.Dependency50.P39.KrausWellDefined
        (attenuatorKraus (Real.exp (-t / 2))) ∧
      ∀ X : BOp, IsTraceClass X →
        TraceHasSum (fun n => krausTerm (attenuatorKraus (Real.exp (-t / 2)) n) X)
          (dampingOutput t X)) ∧
    (∀ m n : ℕ, HasTraceDerivative (fun t => dampingOutput t (fockDyad m n))
      (dampingGeneratorDyad m n) 0) ∧
    IsDensity (fockDyad 0 0) ∧ fockPurity (fockDyad 0 0) = 1 ∧
    (∀ t : ℝ, 0 ≤ t → dampingOutput t (fockDyad 0 0) = fockDyad 0 0) ∧
    (∀ X : BOp, IsDensity X →
      (∀ t : ℝ, 0 ≤ t → IsDensity (dampingOutput t X) ∧
        IsTraceClass (dampingOutput t X - fockDyad 0 0)) ∧
      Tendsto (fun t : ℝ => traceNorm (dampingOutput t X - fockDyad 0 0))
        atTop (nhds 0)) ∧
    ∃ X : BOp, IsDensity X ∧ fockPurity X < 1 ∧
      ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ fockPurity (dampingOutput s X) <
        fockPurity (dampingOutput t X) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P22

end
