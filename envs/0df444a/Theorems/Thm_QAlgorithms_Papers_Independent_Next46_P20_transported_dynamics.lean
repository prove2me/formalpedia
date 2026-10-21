-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_transported_dynamics
-- name    : QAlgorithms.Papers.Independent.Next46.P20.transported_dynamics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:22:43.061595+00:00
-- url     : https://prove2.me/theorems/483e2f33-9947-4419-8e84-c4fb23755a8d
-- title:
--   Equivalence of strong Schrödinger initial-value problems
-- statement:
--   Let $n\ge1$, let $\chi$ be a fixed time-independent unit $L^2$ window, and let $a$ be self-adjoint on its dense domain. Define $A$ by window transport and choose $\psi_0\in D(a)$. A curve $\psi:\mathbb R\to L^2(\mathbb R^n)$ is a strong solution of
--   $$
--   i\dot\psi(t)=a\psi(t),\qquad\psi(0)=\psi_0,
--   $$
--   if and only if $\Psi(t)=T_\chi\psi(t)$ is a strong solution of
--   $$
--   i\dot\Psi(t)=A\Psi(t),\qquad\Psi(0)=T_\chi\psi_0.
--   $$
--   A strong solution lies in the relevant operator domain at every time and has a Hilbert-norm derivative at every real time.
--
--   This states the dynamical correspondence without replacing unbounded evolution by a finite matrix exponential.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 10, Theorem 2.12

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF pp.10–11, Theorem 2.12: strong solutions of the unbounded Schrodinger
initial-value problem correspond under the fixed, time-independent T_chi. -/
theorem transported_dynamics {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n)
    (hSelf : graphSelfAdjointOn (⊤ : Submodule ℂ (ConfigurationL2 n)) (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)))
    (psi0 : a.domain) (curve : ℝ → ConfigurationL2 n) :
    strongSolution (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) curve (psi0 : ConfigurationL2 n) ↔
      strongSolution (transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)))
        (fun t => tensorEmbedding chi (curve t)) (tensorEmbedding chi psi0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
