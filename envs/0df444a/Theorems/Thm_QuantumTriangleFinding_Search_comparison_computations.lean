-- Prove2me | Theorems.Thm_QuantumTriangleFinding_Search_comparison_computations
-- name    : QuantumTriangleFinding.Search.comparison_computations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:03.478724+00:00
-- url     : https://prove2.me/theorems/9c0b2dd6-f938-452f-8a17-20ffbdaab7ca
-- title:
--   Theorem 4.1 — Comparison of computations
-- statement:
--   Let $\rho_-$ be any finite law on Boolean inputs and $\rho_+$ any finite positive-input law, possibly with an inaccessible finite label. Let $V(x,o)$ be a finite search relation with no valid output on the support of $\rho_-$. Suppose $\Upsilon$ acts only on the input register and $\Upsilon|\rho_-\rangle=|\rho_+\rangle$. Suppose $\alpha_e,\beta_e\ge0$ satisfy, for every finite complex workspace and every negative joint vector $f$,
--   $$\|(Q_e^+\Upsilon-\Upsilon Q_e^-)f\|^2\le\alpha_e\|f\|^2+\beta_e\|f\|_\infty^2.$$
--   If candidate outputs admit an exact $v$-query verifier on the combined support domain, then every $t$-query algorithm with actual average positive-law success $\sigma$ satisfies
--   $$\sqrt\sigma\le(t+v)\left(\max_{e\in I}\alpha_e+\sum_{e\in I}\beta_e\right)^{1/2}.$$
--   Verification preserves genuine success and always rejects on negative inputs. The map $\Upsilon$ is arbitrary linear: no positivity, contraction or channel condition is imposed. The output decoder and all algorithm operations are input-independent. The empty maximum is zero, and the idle sector covers zero-coordinate, zero-query circuits.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and square-root probability-weighted joint vectors → Euclidean workspaces and support functions with weighted inner products, norms and kernel adjoints; reason: choosing an orthonormal basis and sending f(x) to √ρ(x)f(x) is an isometric change of coordinates; every finite workspace is represented
--   - encoding: exact v-query verification and ordinary oracle query indices → a family of exact published query circuits on the combined support domain, with a known-zero idle index; reason: finite candidate-controlled circuits can run coherently with their candidate retained; an orthonormal ancillary basis gives Fin k, and the phase-zero branch simulates idle without changing the query count
--   - encoding: arbitrary final measurements in the purified finite quantum query model → published QueryAlg circuits with arbitrary finite ancillas, input-independent final unitaries and basis-output decoders; reason: finite coherent measurement dilation represents every source algorithm with the same query count; starts, gates and decoders are fixed before the oracle input
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), Theorem 4.1, (4.1)–(4.2), p. 16; standing search setup, p. 15

import Definitions.Def_QuantumTriangleFinding_Search_Verification

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Theorem 4.1, p.16, with an operational exact verifier and a label inaccessible to the circuit. -/
theorem comparison_computations {I L O : Type} [Fintype I] [DecidableEq I]
    [Fintype L] [Fintype O] [DecidableEq O]
    (ρn : (I → Bool) → ℝ) (ρp : (L × (I → Bool)) → ℝ)
    (hn : IsProbability ρn) (hp : IsProbability ρp)
    (valid : (I → Bool) → O → Prop)
    (hnegative : ∀ x, 0 < ρn x → ∀ o, ¬ valid x o)
    (Υ : Matrix (Support ρp) (Support ρn) ℂ)
    (hinit : Υ.mulVec (fun _ => 1) = (fun _ => 1))
    (α β : I → ℝ) (hα : ∀ e, 0 ≤ α e) (hβ : ∀ e, 0 ≤ β e)
    (herror : ∀ (W : Type) [Fintype W] (e : I) (f : Joint ρn W),
      normSq ρp (applyKernel
        (inputPhase ρp Prod.snd e * Υ - Υ * inputPhase ρn id e) f) ≤
        α e * normSq ρn f + β e * infinityNorm ρn f ^ 2)
    (v : ℕ) (hverifier : HasExactVerifier (comparisonDomain ρn ρp) valid v)
    (t : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (A : QAlgorithms.QueryAlg (Option I) Bool W t)
    (out : ((Option I × Bool) × W) → O) :
    Real.sqrt (∑ z, ρp z * relationSuccess valid z.2 A out) ≤
      ((t : ℝ) + (v : ℝ)) * Real.sqrt (maxCoefficient α + ∑ e, β e) := by sorry

end QuantumTriangleFinding.Search
