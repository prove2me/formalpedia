-- Prove2me | Theorems.Thm_ResultantVNP_lemma_2_6_3
-- name    : ResultantVNP.lemma_2_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:16.115214+00:00
-- url     : https://prove2.me/theorems/75bf83c2-7666-4d8d-a310-e465fbb54a9c
-- title:
--   Lemma 2.6(3) — variable scaling
-- statement:
--   Let $n\ge1$ and let $f_1,\dots,f_n$ be homogeneous forms of degrees $d_1,\dots,d_n\ge1$. For every complex $n\times n$ matrix $Q$, writing $f_i(Qx)$ for $f_i$ with $x_k$ replaced by $\sum_j Q_{kj}x_j$,
--
--   $$
--   \mathrm{Res}\big(f_1(Qx),\dots,f_n(Qx)\big)=(\det Q)^{\prod_{j=1}^n d_j}\,\mathrm{Res}(f_1,\dots,f_n).
--   $$
--
--   Differences from the source:
--   - encoding: the multivariate resultant Res, the unique integral polynomial with the three properties of Definition 2.1 (existence and uniqueness cited from [GKZ94]) → an arbitrary ResultantSystem 𝓡 (integral polynomials satisfying the three properties for n ≥ 1 and positive degrees), quantified universally; reason: existence is cited, not proved in the paper; by uniqueness every resultant system is the resultant on every admissible degree vector, so the statement is the paper's
--   - encoding: standing assumptions of Definition 2.1 (positive integer degrees, n forms in n variables) → hypotheses n ≥ 1 and positive degrees d_i; reason: Definition 2.1 assumes them; the resultant is undefined otherwise (no resultant exists for n = 0)
--   - encoding: Res(f₁, …, fₙ) of homogeneous forms → resOf 𝓡 d f: Res_d evaluated at the coefficients [x^e] f_i, |e| = d_i, with each f_i assumed homogeneous of degree d_i; reason: the notation of Definition 2.1 (evaluation at the coefficients of the forms)
--   - encoding: indices [n] = {1, …, n} → Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Lemma 2.6(3), p.12

import Mathlib
import Definitions.Def_ResultantVNP_resOf

namespace ResultantVNP

/-- **Lemma 2.6(3) (Variable scaling).** Let `f₁, …, fₙ` be homogeneous forms of degrees `d₁, …, dₙ`.
For every `n × n` matrix `Q`, `Res(f₁(Qx), …, fₙ(Qx)) = (det Q)^{∏_j d_j} Res(f₁, …, fₙ)`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Lemma 2.6(3), p.12.

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡`; by the uniqueness in Definition 2.1 it is the multivariate resultant wherever the paper uses it. `f_i(Qx)` substitutes `x_k ↦ ∑_j Q_{kj} x_j`. `n ≥ 1`, degrees positive. -/
theorem lemma_2_6_3 (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (f : Fin n → MvPolynomial (Fin n) ℂ) (hf : ∀ i, (f i).IsHomogeneous (d i))
    (Q : Matrix (Fin n) (Fin n) ℂ) :
    resOf 𝓡 d (fun i => MvPolynomial.aeval
        (fun k => ∑ j, MvPolynomial.C (Q k j) * MvPolynomial.X j) (f i)) =
      Q.det ^ (∏ j, d j) * resOf 𝓡 d f := by sorry

end ResultantVNP
