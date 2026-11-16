-- Prove2me | Theorems.Thm_QuantumStateIdentity321_Schur_Supplement_lemma_3_1
-- name    : QuantumStateIdentity321.Schur.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:49.32048+00:00
-- url     : https://prove2.me/theorems/ca05b2c0-3d3e-49ef-92e0-4a8ea5216289
-- title:
--   Lemma 3.1 — geometric witness: a pair with fidelity at most $\varepsilon$ makes every other state far from one of its endpoints
-- statement:
--   Let $|\psi_1\rangle,\dots,|\psi_n\rangle$ be pure states (unit vectors of $\mathbb C^d$) and write $F_{ij}=|\langle\psi_i|\psi_j\rangle|^2$. Suppose two distinct indices $a\ne b$ satisfy $F_{ab}\le\varepsilon$. Then for every $r\in[n]\setminus\{a,b\}$,
--
--   $$
--   \min\{F_{ar},F_{br}\}\le\frac{1+\sqrt\varepsilon}2 .
--   $$
--
--   A single bad pair therefore cannot be isolated from the other states: every other index forms a **witness edge** with $a$ or with $b$. This is what lets Algorithm 2 detect a no instance by testing random edges instead of the unknown bad pair.
--
--   Differences from the source:
--   - generalization: ε ∈ (0, 1/4) (the standing range of §3; the lemma itself states no range) → every real ε; reason: the bound needs no range: it is vacuous for ε < 0 (F_ab ≥ 0) and trivial for ε ≥ 1 (F ≤ 1); it specializes to every ε in the source range
--   - generalization: n ≥ 2 states of local dimension d ≥ 2 (Definition 1.1's standing assumption) → every n and d; reason: for n ≤ 2 there is no r and the statement is empty, and the bound holds in every dimension; it specializes to every n ≥ 2, d ≥ 2
--   - encoding: indices $1,\dots,n$ → `Fin n`, label $i$ is the source's $i+1$; reason: Lean convention; same instances
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), Lemma 3.1, PDF/printed p.9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Model

namespace QuantumStateIdentity321.Schur.Supplement

/-- Lemma 3.1 (geometric witness lemma), p.9: if two distinct inputs `a ≠ b` have fidelity
`F_ab = |⟨ψ_a|ψ_b⟩|² ≤ ε`, then every other input `r ∉ {a, b}` satisfies
`min{F_ar, F_br} ≤ (1 + √ε)/2`. -/
theorem lemma_3_1 {n d : ℕ} (ψ : Fin n → State d) (hψ : ∀ i, ‖ψ i‖ = 1) (ε : ℝ)
    (a b : Fin n) (hab : a ≠ b) (hF : fidelity (ψ a) (ψ b) ≤ ε) :
    ∀ r : Fin n, r ≠ a → r ≠ b →
      min (fidelity (ψ a) (ψ r)) (fidelity (ψ b) (ψ r)) ≤ (1 + Real.sqrt ε) / 2 := by sorry

end QuantumStateIdentity321.Schur.Supplement
