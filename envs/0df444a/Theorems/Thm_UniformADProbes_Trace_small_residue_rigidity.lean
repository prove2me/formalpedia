-- Prove2me | Theorems.Thm_UniformADProbes_Trace_small_residue_rigidity
-- name    : UniformADProbes.Trace.small_residue_rigidity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:07.983494+00:00
-- url     : https://prove2.me/theorems/48250530-d4a0-4501-8a3c-7ca782b96e18
-- title:
--   Lemma 2.1 — Small-residue rigidity
-- statement:
--   Let $n\ge0$, let $B,H\in M_n(\mathbb R)$ be symmetric, and let $V\subseteq\mathbb R(t)^n$ be a rational-function-linear subspace invariant under $\nabla f=f'+(B/t+H)f$. Write $r=\dim_{\mathbb R(t)}V$. If
--   $$r\,\operatorname{diam}\operatorname{Spec}(B)<1,$$
--   then there is a real subspace $W\subseteq\mathbb R^n$, invariant under both $B$ and $H$, such that
--   $$V=\operatorname{span}_{\mathbb R(t)}W.$$
--   The dimension-zero and full-dimension cases are included. The conclusion identifies a rational invariant subspace with the scalar extension of a constant one; the connection is not assumed rational-function linear.
--
--   Differences from the source:
--   - encoding: real matrix spaces and scalar extension → coordinates Fin n and the rational-function span of embedded real vectors; reason: finite coordinate identification; scalar extension has its usual concrete meaning
--   - generalization: the usual positive matrix orders → also zero ambient dimension; reason: the zero-dimensional rational and real spaces are both zero, so this additional case is immediate
--   - encoding: r is the dimension; diameter is the extremal eigenvalue difference → r is finrank of V and diameter is sSup spectrum minus sInf spectrum; reason: finite-dimensional V and the nonempty finite real spectrum of a symmetric matrix make both exact
--   - encoding: formal derivative f′ on ℝ(t) → the quotient rule applied to the canonical numerator and denominator of RatFunc ℝ, coordinatewise; reason: this is the usual derivation of the rational function field; no instance changes
-- source:
--   Zhipeng Lu, Uniform adjacency-degree probes from differential rigidity, STOC 2027 submission #25 (October 2026), Lemma 2.1, p. 5 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/25.pdf

import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false

namespace UniformADProbes.Trace

theorem small_residue_rigidity (n : ℕ)
    (B H : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (hH : H.IsSymm)
    (V : Submodule (RatFunc ℝ) (Fin n → RatFunc ℝ))
    (hinv : ∀ f ∈ V, connection B H f ∈ V)
    (hsmall : (Module.finrank (RatFunc ℝ) V : ℝ) * spectralDiameter B < 1) :
    ∃ W : Submodule ℝ (Fin n → ℝ),
      V = scalarExtension W ∧ MatrixInvariant W B ∧ MatrixInvariant W H := by sorry

end UniformADProbes.Trace
