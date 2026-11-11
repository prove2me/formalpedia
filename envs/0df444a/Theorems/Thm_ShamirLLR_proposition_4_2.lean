-- Prove2me | Theorems.Thm_ShamirLLR_proposition_4_2
-- name    : ShamirLLR.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:28:32.514407+00:00
-- url     : https://prove2.me/theorems/b894081d-c1a2-42dd-84cb-83cab540203c
-- title:
--   Proposition 4.2 — approximation and closure of $G_{p,3}$ (every accuracy $\eta$)
-- statement:
--   1. For every $\eta>0$ there is a choice of class data — a nonempty finite collection $\mathcal N$ of degree-two filtered nilmanifolds, an integer $D\ge1$ bounding their dimensions, and $Q\ge1$ — such that for every odd prime $p$ and every one-bit leakage function $f:\mathbb F_p\to\{0,1\}$ there is $f_{\mathrm{nil}}\in G_{p,3}$ with
--   $$
--   \|f-f_{\mathrm{nil}}\|_{U^3}<\eta .
--   $$
--   2. For every choice of class data with $Q\ge1$ and every odd prime $p$, the class $G_{p,3}$ is closed under complements $g\mapsto1-g$ and under bijective affine precompositions $g\mapsto g(\lambda\,\cdot+\mu)$, $\lambda\in\mathbb F_p^*$, $\mu\in\mathbb F_p$.
--
--   The first part makes $G_{p,3}$ an approximation class for Lemma 2.1; the second supplies its affine-closure hypothesis.
--
--   Differences from the source:
--   - generalization: accuracy $\eta=2^{-24/(c-1/3)^2}$ with data depending only on $c$ → every accuracy $\eta>0$, with data depending only on $\eta$; reason: specializes at $\eta=\eta(c)$; the proof of Theorem 1 uses the construction at $\eta=2^{-3/\alpha}$ and states it "works for every fixed positive accuracy" (p.65)
--   - encoding: the class data of §4.1 → $\mathcal N$ a finite nonempty set of `LSS.Nilmanifold 2`, $D\ge1$ with all dimensions $\le D$, $Q\ge1$, as explicit conclusions; reason: §4.1 fixes exactly these data
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Proposition 4.2, p.27 (PDF p.28); proof of Theorem 1, Step 1, p.65 (PDF p.66)

import Mathlib
import Definitions.Def_LSSNil
import Definitions.Def_ShamirLLR_leakageLaws
import Definitions.Def_ShamirLLR_gowersU3
import Definitions.Def_ShamirLLR_classG

set_option autoImplicit false

namespace ShamirLLR

/-- **Proposition 4.2 (Approximation and closure), at every accuracy `η > 0`.**
1. For every `η > 0` there is a choice of class data `N` (a nonempty finite collection of
   degree-two filtered nilmanifolds), `D ≥ 1` bounding their dimensions and `Q ≥ 1` such that for
   every odd prime `p` and every one-bit leakage function `f : 𝔽_p → {0, 1}` there is
   `f_nil ∈ G_{p,3}` with `‖f − f_nil‖_{U³} < η`.
2. For every choice of class data with `Q ≥ 1` and every odd prime `p`, the class `G_{p,3}` is
   closed under complements `g ↦ 1 − g` and bijective affine precompositions
   `g ↦ g(λ · + μ)`, `λ ≠ 0`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Proposition 4.2, p.27 (stated at `η = 2^{−24/(c−1/3)²}`); the proof of Theorem 1, Step 1, p.65:
"That construction works for every fixed positive accuracy".

**Formalization Note.** `G_{p,3}` is `classG p N D Q` (Definition 4.1, `R = 2D + 4`); `N` is a
finite nonempty set of `LSS.Nilmanifold 2`. -/
theorem proposition_4_2 :
    (∀ η : ℝ, 0 < η → ∃ (N : Set (LSS.Nilmanifold 2)) (D : ℕ) (Q : ℝ),
        N.Finite ∧ N.Nonempty ∧ 1 ≤ D ∧ (∀ G ∈ N, G.d ≤ D) ∧ 1 ≤ Q ∧
        ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ f : ZMod p → Bool, ∃ g ∈ classG p N D Q,
          gowersU3 (fun z => ((bitMap f z - g z : ℝ) : ℂ)) < η) ∧
      ∀ (N : Set (LSS.Nilmanifold 2)) (D : ℕ) (Q : ℝ), 1 ≤ Q → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        ∀ g ∈ classG p N D Q, (fun z => 1 - g z) ∈ classG p N D Q ∧
          ∀ l μ : ZMod p, l ≠ 0 → (fun z => g (l * z + μ)) ∈ classG p N D Q := by sorry

end ShamirLLR
