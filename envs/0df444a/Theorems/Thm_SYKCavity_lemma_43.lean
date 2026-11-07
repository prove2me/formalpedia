-- Prove2me | Theorems.Thm_SYKCavity_lemma_43
-- name    : SYKCavity.lemma_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:35:41.1282+00:00
-- url     : https://prove2.me/theorems/2cf4ebf5-a013-49c6-a7f8-18655a26630d
-- title:
--   Lemma 43 — exact orthogonal reconstruction of $\langle\chi_{j_1}(t_1)\cdots\chi_{j_{2k}}(t_{2k})P(Q)\rangle_N$ from moments of $Q$ via $\mathcal G_{k,N}^{-1}$
-- statement:
--   Let $\beta\ge0$, $N\ge k$, and let $P(Q)$ be a polynomial in finitely many collective variables $Q_{uv}$. Then $\mathcal G_{k,N}$ (4.5) is invertible and
--   $$\langle\chi_{j_1}(t_1)\cdots\chi_{j_{2k}}(t_{2k})P(Q)\rangle_N=2^k\sum_{\pi,\sigma\in\mathcal P_2([2k])}\Bigl(\prod_{\{a,b\}\in\pi}\delta_{j_aj_b}\Bigr)(\mathcal G_{k,N}^{-1})_{\pi\sigma}(-1)^{\operatorname{cr}(\sigma)}\Bigl\langle P(Q)\prod_{\{a,b\}\in\sigma,\,a<b}Q_{t_at_b}\Bigr\rangle_N.\qquad(E.13)$$
--   The identity holds for distinct times, for the alternating values of Lemma 42, and for ordered limits obtained from distinct times.
--
--   It reduces every correlator needed by the coefficients (4.1) to moments of the collective variables $Q$, which the hierarchy (4.9) then determines.
--
--   **Formalization Note** $P$ is taken to be a monomial $\prod_{l<L}Q_{u_lv_l}$ (repetitions allowed); both sides are linear in $P$. Ordered limits use offsets distinct on all occurrences, and on the right the factor $Q_{t_at_b}$ carries the offsets of occurrences $a,b$. Times are arbitrary reals (points of the thermal circle).
--
--   Differences from the source:
--   - encoding: the SYK Hamiltonian of Section 3, ψ_i Majoranas with {ψ_i, ψ_j} = 2δ_ij I → H = √(3/(8N³)) Σ_A J_A Γ_A with ψ_i the first N Jordan–Wigner generators on ⌈N/2⌉ qubits, sites Fin N; reason: standard representation (unique up to equivalence for even N); every milestone is a disorder average or uses Section 3's Γ-form as printed
--   - encoding: ⟨·⟩_N as the Grassmann ratio (3.19) → the trace-side expression (3.20) with Lemma 42's prescriptions (E.1)–(E.4), as the definition; reason: the page proves the two agree (3.20, Lemma 42); planning decision recorded for the moderator
--   - encoding: P(Q) a polynomial in finitely many collective variables → P a monomial ∏_{l<L} Q_{u_l v_l} (repetitions allowed); reason: both sides are linear in P, so the monomial case is the polynomial case
--   - generalization: (E.13), which uses G_{k,N}^{−1} → the conclusion also asserts that G_{k,N} is invertible (IsUnit det); reason: (E.13) presupposes the inverse; stating it excludes the junk value of `Matrix.inv`, and the identity is the page's
--   - encoding: "ordered limits obtained from distinct times" → offsets η injective on all 2k + 2L occurrences; the right side's Q_{t_a t_b} inherit the offsets of a and b; reason: the ordered limit t + εη, ε ↓ 0, of Lemma 42; the right side is evaluated along the same perturbed times
--   - encoding: times t_a, u_l, v_l on the thermal circle → arbitrary real times, reduced by (E.4); reason: points of ℝ/ℤ
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), Lemma 43, p.97, (E.13); (4.5)–(4.6), p.26; Lemma 42, p.95

import Mathlib
import Definitions.Def_SYKCavity_Correlator
import Definitions.Def_SYKCavity_Pairing

open MeasureTheory

namespace SYKCavity

/-- **Lemma 43 (Exact orthogonal reconstruction)**, p.97 of A. Schmidhuber, A. Zlokapa,
*Polynomial-time algorithms for mean-field models up to the glass transition*, arXiv:2610.06807
(held version, sha256 25d817ba…cfc5), (E.13).

Let `N ≥ k` and let `P(Q) = ∏_{l<L} Q_{u_l v_l}` be a monomial in finitely many collective variables
(repetitions allowed). Then `G_{k,N}` is invertible and
`⟨χ_{j_1}(t_1) ⋯ χ_{j_{2k}}(t_{2k}) P(Q)⟩_N
  = 2^k Σ_{π,σ ∈ P2([2k])} (∏_{{a,b} ∈ π} δ_{j_a j_b}) (G_{k,N}^{−1})_{πσ} (−1)^{cr(σ)}
      ⟨P(Q) ∏_{{a,b} ∈ σ, a<b} Q_{t_a t_b}⟩_N`,
both for the alternating values of Lemma 42 (which include distinct times) and for every ordered
limit obtained from distinct times (offsets `η` distinct on all occurrences; the factor `Q_{t_a t_b}`
on the right carries the offsets of occurrences `a` and `b`).

**Formalization Note.** `⟨·⟩_N` is `qAlt`/`qOrd` (trace side, Lemma 42 prescriptions, Section 3's `H`).
Both sides are linear in `P`, so the monomial case is the statement for every polynomial `P`. Times
are arbitrary reals (points of the thermal circle). The invertibility of `G_{k,N}`, which (E.13)
presupposes, is stated as part of the conclusion; `Matrix.inv` is the matrix inverse. -/
theorem lemma_43 (β : ℝ) (hβ : 0 ≤ β) (k N : ℕ) (hkN : k ≤ N) (L : ℕ)
    (j : Fin (2 * k) → Fin N) (t : Fin (2 * k) → ℝ) (u v : Fin L → ℝ) :
    IsUnit (Gmat k N).det ∧
    qAlt β N j t u v =
      2 ^ k * ∑ π : Pairing k, ∑ σ : Pairing k,
        ((deltaProd j π * (Gmat k N)⁻¹ π σ : ℝ) : ℂ) * (-1 : ℂ) ^ cross σ *
          qAlt β N (m := 0) Fin.elim0 Fin.elim0
            (Fin.append u (fun l => t (σ.1 l).1)) (Fin.append v (fun l => t (σ.1 l).2)) ∧
    ∀ (ηt : Fin (2 * k) → ℝ) (ηu ηv : Fin L → ℝ),
      Function.Injective (Fin.append ηt (pairList ηu ηv)) →
      qOrd β N j t ηt u v ηu ηv =
        2 ^ k * ∑ π : Pairing k, ∑ σ : Pairing k,
          ((deltaProd j π * (Gmat k N)⁻¹ π σ : ℝ) : ℂ) * (-1 : ℂ) ^ cross σ *
            qOrd β N (m := 0) Fin.elim0 Fin.elim0 Fin.elim0
              (Fin.append u (fun l => t (σ.1 l).1)) (Fin.append v (fun l => t (σ.1 l).2))
              (Fin.append ηu (fun l => ηt (σ.1 l).1)) (Fin.append ηv (fun l => ηt (σ.1 l).2)) := by sorry

end SYKCavity
