-- Prove2me | Theorems.Thm_QThermalClassical_lemma_13
-- name    : QThermalClassical.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:20.902294+00:00
-- url     : https://prove2.me/theorems/72ea3f82-0aa2-4704-8904-5d6adb8204b2
-- title:
--   Lemma 13 — coefficient control $|c_i|\le q^{|u_S(X_i)|}$
-- statement:
--   Suppose the sampling primitive satisfies $|b_i|\le L(\beta/2)\,q^{t_i}$ with
--   $$
--   0<q<1,\qquad\frac{6L(\beta/2)}{1-q}\le1\qquad(94),
--   $$
--   where $t_i=|C(E_i)|$, and Algorithm 1 uses $p_1=q$, $p_{J}=(1-q)/6$ ($J\neq1$). Then at each step of the algorithm each monomial satisfies
--   $$
--   |c_i|\le q^{|u_S(X_i)|}\qquad(95),
--   $$
--   in the form: one iteration (for any admissible $a^*$, any outcomes obeying the bound and any branch $J$) maps a configuration satisfying (95) for $S$ to one satisfying (95) for $\hat S$ (the empty starting configuration satisfies (95)). Furthermore at the end of the algorithm $|c_i|\le1$ for all monomials: every configuration satisfying (95) has $|c_i|\le1$.
--
--   Together with Lemma 10 this bounds every factor of the final configuration by $|c_i|\le1$.
--
--   Differences from the source:
--   - reading: "at each step of the algorithm each monomial satisfies (95)" → one iteration preserves (95); reason: the proof shows exactly this, by cases over $J$; the loop starts from the empty configuration
--   - generalization: outcomes of the sampling primitive inside a run of the algorithm → any two outcomes obeying $|b|\le Lq^{|C|}$, any admissible $a^*$, any branch $J$, any configuration; reason: the proof uses only these facts; it specializes to runs of the algorithm
--   - reading: "at the end of the algorithm $|c_i|\le1$" → every configuration satisfying (95) has $|c_i|\le1$; reason: the proof's last sentence derives it from (95) and $q<1$; at the end (95) holds
--   - encoding: $L(\beta/2)$ → a real number $L$; reason: only its value at $\beta/2$ enters
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 13, eqs. (94)–(95), pp.30–32; Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_pinStep

set_option autoImplicit false

namespace QThermalClassical

/-- **Lemma 13 (Coefficient control).** If the sampling primitive satisfies
`|bᵢ| ≤ L(β/2) q^{tᵢ}` with `0 < q < 1` and `6L(β/2)/(1 − q) ≤ 1` (94), then at each step of
Algorithm 1 each monomial satisfies `|cᵢ| ≤ q^{|u_S(Xᵢ)|}` (95); furthermore at the end of the
algorithm `|cᵢ| ≤ 1` for all monomials.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 13, eqs. (94)–(95), p.30; Algorithm 1, p.27.

**Formalization Note.** `L` is the real number `L(β/2)`. "At each step" is stated as an
invariant: the configuration is empty at the start, and the first clause says one iteration
(any admissible `a*`, any outcomes obeying the bound with `tᵢ = |C(Eᵢ)|`, any branch `J`,
with the branch probabilities `p₁ = q`, `p_{≠1} = (1 − q)/6` of line 10) preserves (95). The
second clause gives `|cᵢ| ≤ 1` from (95), in particular at the end of the algorithm. -/
theorem lemma_13 {Q : Type} [Fintype Q] [DecidableEq Q] (c : PauliWord Q → ℝ) (q L : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hL : 6 * L / (1 - q) ≤ 1) :
    (∀ (S : Finset Q) (χ : Config Q) (a : PauliWord Q), IsAdmissible c S χ a →
      ∀ o₁ o₂ : Outcome Q, |o₁.b| ≤ L * q ^ o₁.C.length → |o₂.b| ≤ L * q ^ o₂.C.length →
      ∀ J : Fin 7,
        (∀ e ∈ χ, |e.coeff| ≤ q ^ (uSet S e.terms).card) →
        ∀ e ∈ (pinStep q S χ a o₁ o₂ J).2,
          |e.coeff| ≤ q ^ (uSet (pinStep q S χ a o₁ o₂ J).1 e.terms).card) ∧
    (∀ (S : Finset Q) (χ : Config Q), (∀ e ∈ χ, |e.coeff| ≤ q ^ (uSet S e.terms).card) →
      ∀ e ∈ χ, |e.coeff| ≤ 1) := by sorry

end QThermalClassical
