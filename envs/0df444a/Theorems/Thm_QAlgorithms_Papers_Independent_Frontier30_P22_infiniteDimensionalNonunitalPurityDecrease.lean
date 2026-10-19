-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P22_infiniteDimensionalNonunitalPurityDecrease
-- name    : QAlgorithms.Papers.Independent.Frontier30.P22.infiniteDimensionalNonunitalPurityDecrease
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:24:22.922255+00:00
-- url     : https://prove2.me/theorems/cc7b645e-ecca-4ec5-8fd2-8ed466fc4147
-- title:
--   An infinite-dimensional nonunital purity-decreasing semigroup
-- statement:
--   On the full one-mode Fock space $\ell^2(\mathbb N)$, there exists a proper isometry $V$ satisfying $V|n\rangle=|n+1\rangle$. With $P_0=|0\rangle\langle0|$, it obeys $V^\dagger V=I$ and $VV^\dagger=I-P_0$. For the bounded single-jump generator
--   $$
--   G(X)=VXV^\dagger-X,\qquad\Phi_t=e^{tG},
--   $$
--   the maps $\Phi_t$, $t\ge0$, form a completely positive trace-preserving semigroup, have density outputs for all trace-class density inputs, and satisfy
--   $$
--   p(\Phi_t(\rho))\le p(\Phi_s(\rho))\quad(0\le s\le t),\qquad G(I)=-P_0\ne0.
--   $$
--   The Kraus family $K_n(t)=e^{-t/2}\sqrt{t^n/n!}\,V^n$ is normalized and its action sums to $\Phi_t$ in trace norm for every trace-class input.
--
--   Thus universal purity nonincrease does not force unitality in infinite dimension.
-- source:
--   Conditions for strictly purity-decreasing quantum Markovian dynamics, arXiv:quant-ph/0411119v2, PDF p. 3, Corollary 1

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

/-- Corollary 1, PDF p.3: an infinite-dimensional nonunital, purity-nonincreasing
quantum Markov semigroup exists. The proper unilateral isometry explicitly used
in Section IV supplies a bounded witness, without truncating the Fock space.
Its formal identity image is minus the vacuum projection, not zero. -/
theorem infiniteDimensionalNonunitalPurityDecrease :
    ∃ V : BOp,
      (∀ n : ℕ, V (fockKet n) = fockKet (n + 1)) ∧
      V.adjoint * V = 1 ∧ V * V.adjoint = 1 - fockDyad 0 0 ∧
      properIsometryGenerator V 1 = -fockDyad 0 0 ∧
      properIsometryGenerator V 1 ≠ 0 ∧
      (∀ t : ℝ, 0 ≤ t →
        QAlgorithms.Papers.Independent.Dependency50.P39.KrausWellDefined
          (properIsometryKraus V t) ∧
        ∀ X : BOp, IsTraceClass X →
          TraceHasSum (fun n => krausTerm (properIsometryKraus V t n) X)
            (properIsometryEvolution V t X)) ∧
      ∀ X : BOp, IsDensity X →
        (∀ t : ℝ, 0 ≤ t → IsDensity (properIsometryEvolution V t X)) ∧
        AntitoneOn (fun t : ℝ => fockPurity (properIsometryEvolution V t X))
          (Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P22

end
