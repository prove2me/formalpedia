-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_5_3
-- name    : PosIndexNash.PPADS.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:18.977767+00:00
-- url     : https://prove2.me/theorems/9039a0bd-9a01-4078-913d-9b7c1fca2108
-- title:
--   Lemma 5.3 — exact correspondence: Fix(Φ) ↔ Sol(LCP(M, −b)) via λ ↦ x(λ) and x ↦ Vᵀx
-- statement:
--   Let a max-affine circuit be given in normal form (31) with anchored outputs (32)/(35), computing $\Phi(\lambda) = V^\top x(\lambda)$, and let $M = A - UV^\top$ (36). There is a bijection
--   $$\mathrm{Fix}(\Phi) \longleftrightarrow \mathrm{Sol}\big(\mathrm{LCP}(M, -b)\big):$$
--   the forward map sends a fixed point $\lambda \in [0,1]^d$ to the circuit execution $x(\lambda)$, and the inverse map is $x \mapsto V^\top x$. In Lean: $x(\lambda)$ solves the LCP for every fixed point $\lambda$; $V^\top x$ is a fixed point for every solution $x$; and $V^\top x(\lambda) = \lambda$, $x(V^\top x) = x$.
--
--   This turns fixed points of the circuit into solutions of a single LCP (39), the first step of the hardness reduction.
--
--   Differences from the source:
--   - generalization: "$\Phi$ and its rational max-affine circuit from Theorem 4.2", brought to normal form → every max-affine circuit in normal form with anchored outputs; reason: the proof uses only (33)–(35); the circuit of Theorem 4.2 in normal form is one such circuit, so the statement specializes to the paper's.
--   - encoding: "a bijection with forward map $x(\lambda)$ and inverse $x\mapsto V^\top x$" → the two maps land in the right sets and are mutually inverse; reason: this is what the bijection with those maps means.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 37, Lemma 5.3

import Mathlib
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP

open Matrix

namespace PosIndexNash.PPADS

theorem lemma_5_3 (F : NormalForm) (hF : F.Anchored) :
    (∀ lam ∈ F.Fix,
      F.exec lam ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ)))) ∧
    (∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      (F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x ∈ F.Fix) ∧
    (∀ lam ∈ F.Fix, (F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ F.exec lam = lam) ∧
    (∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      F.exec ((F.V.map ((↑) : ℚ → ℝ))ᵀ *ᵥ x) = x) := by sorry

end PosIndexNash.PPADS
