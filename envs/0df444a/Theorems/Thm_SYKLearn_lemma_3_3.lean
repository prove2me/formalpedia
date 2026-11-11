-- Prove2me | Theorems.Thm_SYKLearn_lemma_3_3
-- name    : SYKLearn.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:25.461643+00:00
-- url     : https://prove2.me/theorems/d98698d8-87af-4251-99b7-61feb31fd5de
-- title:
--   Lemma 3.3 — low-degree decomposition: $\Pi_1\bar\rho_4=-c_{1,4}H_g$, $\Pi_2\bar\rho_k=c_{2,k}H^2|_{\mathbb M_k}$, $\Pi_3\bar\rho_8=-c^{\rm conn}_{3,8}T_{\rm conn}+c^{\rm dis}_{3,8}T_{\rm dis}$
-- statement:
--   Let $\bar\rho_4,\bar\rho_8$ be the degree-$4$ and degree-$8$ components of the annealed Gibbs state $e^{-\beta H_g}/\mathbb E_g\mathrm{Tr}[e^{-\beta H_g}]$, viewed as functions of the Gaussian couplings, and let $\Pi_d$ be the projection onto Hermite degree $d$. Then the coefficients $c_{1,4},c_{2,4},c_{2,8},c^{\rm conn}_{3,8},c^{\rm dis}_{3,8}$, which depend only on $n,\beta$, satisfy, for every coupling vector $g$,
--
--   $$\Pi_1\bar\rho_4=-c_{1,4}H_g,\qquad \Pi_2\bar\rho_4=c_{2,4}\big(H^2|_{\mathbb M_4}\big),\qquad \Pi_2\bar\rho_8=c_{2,8}\big(H^2|_{\mathbb M_8}\big),\qquad \Pi_3\bar\rho_8=-c^{\rm conn}_{3,8}T_{\rm conn}+c^{\rm dis}_{3,8}T_{\rm dis},$$
--
--   so that
--
--   $$\Pi_{d\le2}\bar\rho_4+\Pi_{d\le3}\bar\rho_8=-c_{1,4}H_g+c_{2,4}\big(H^2|_{\mathbb M_4}\big)+c_{2,8}\big(H^2|_{\mathbb M_8}\big)-c^{\rm conn}_{3,8}T_{\rm conn}+c^{\rm dis}_{3,8}T_{\rm dis},$$
--
--   where $T_{\rm dis}=g\wedge(H^2|_{\mathbb M_4})$ and $T_{\rm conn}=\sum_{i,j}a_ig\wedge a_ja_ig\wedge a_jg$. Moreover, for a universal constant $C$,
--
--   $$|c_{1,4}|\le C\beta,\qquad |c_{2,4}|+|c_{2,8}|\le C\beta^2,\qquad |c^{\rm conn}_{3,8}|+|c^{\rm dis}_{3,8}|\le C\beta^3 .$$
--
--   The summed identity also records that the Hermite components $\Pi_0\bar\rho_4$, $\Pi_0\bar\rho_8$, $\Pi_1\bar\rho_8$ vanish. The lemma isolates the leading signal $-c_{1,4}H_g$ and the one competing term $T_{\rm conn}$ in the commutator gap.
--
--   **Formalization Note** The coefficients are the canonical ($L^2$ least-squares) ones of the definition module. Vectors of $\mathbb M_4$ such as $H_g$ are the coupling vector $|g\rangle$. $C$ is chosen before $\beta$ and $n$. Stated for $\beta>0$ and every even $n\ge10$.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: there are coefficients c_{1,4}, c_{2,4}, c_{2,8}, c^dis_{3,8}, c^conn_{3,8} depending only on n, β → the canonical L² least-squares coefficients c14, c24, c28, cconn, cdis; reason: if the identities hold with some coefficients, the canonical ones satisfy them too (a regressor that is not identically zero determines its coefficient; the minimum-norm solution of the pair has norm at most that of any exact solution, so the bounds hold with C enlarged by √2); conversely the canonical ones are coefficients
--   - reading: no size condition on n is printed in Lemma 3.3 → every even N ≥ 10; reason: the lemma's proof is Lemma A.5 (p.51), stated for n ≥ (4d + k)/2, which is 10 at (d, k) = (3, 8); every use of Lemma 3.3 is for large n
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 3.3, p.20 (proof pp.20–21, via Lemma A.5, p.51)

import Mathlib
import Definitions.Def_SYKLearn_Coefficients

noncomputable section
open SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 3.3 (Low-degree decomposition)**, p.20 (Anshu–Arunachalam–Chen–Hwang, *Efficiently
Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). Let
`R = ρ̄_4 + ρ̄_8` (annealed components). There are coefficients `c_{1,4}, c_{2,4}, c_{2,8},
c^dis_{3,8}, c^conn_{3,8}` depending only on `n, β` such that `Π_1ρ̄_4 = −c_{1,4}H_g`,
`Π_2ρ̄_4 = c_{2,4}(H²|M_4)`, `Π_2ρ̄_8 = c_{2,8}(H²|M_8)`,
`Π_3ρ̄_8 = −c^conn_{3,8}T_conn + c^dis_{3,8}T_dis`, so that
`Π_{d≤2}ρ̄_4 + Π_{d≤3}ρ̄_8 = −c_{1,4}H_g + c_{2,4}(H²|M_4) + c_{2,8}(H²|M_8) − c^conn_{3,8}T_conn +
c^dis_{3,8}T_dis`. Moreover `|c_{1,4}| ≤ Cβ`, `|c_{2,4}| + |c_{2,8}| ≤ Cβ²`,
`|c^conn_{3,8}| + |c^dis_{3,8}| ≤ Cβ³`.

**Formalization Note.** The coefficients are the canonical ones of
`Definitions.Def_SYKLearn_Coefficients` (least-squares projections in `L²` of the coupling law),
which are the paper's whenever its identities hold with linearly independent regressors. `C` is
universal (chosen before `β` and `n`). The identities are equalities of functions of the coupling
vector, stated at every `w`. The lemma is stated for `N ≥ 10`, the size condition
`n ≥ (4d + k)/2` of Lemma A.5 (p.51) at `(d, k) = (3, 8)` on which its proof rests. `Q.J = 1`; every
CAR family. -/
theorem lemma_3_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∀ (N : ℕ) (Q : Model N), 10 ≤ N → Q.J = 1 →
      (∀ w, proj Q 1 (rhoK β Q 4) w = -(c14 β Q) • emb4 w) ∧
      (∀ w, proj Q 2 (rhoK β Q 4) w = c24 β Q • Hsq4 Q w) ∧
      (∀ w, proj Q 2 (rhoK β Q 8) w = c28 β Q • Hsq8 Q w) ∧
      (∀ w, proj Q 3 (rhoK β Q 8) w = -(cconn β Q) • Tconn w + cdis β Q • Tdis Q w) ∧
      (∀ w, (∑ d ∈ Finset.range 3, proj Q d (rhoK β Q 4) w) +
          (∑ d ∈ Finset.range 4, proj Q d (rhoK β Q 8) w) =
        -(c14 β Q) • emb4 w + c24 β Q • Hsq4 Q w + c28 β Q • Hsq8 Q w +
          -(cconn β Q) • Tconn w + cdis β Q • Tdis Q w) ∧
      |c14 β Q| ≤ C * β ∧
      |c24 β Q| + |c28 β Q| ≤ C * β ^ 2 ∧
      |cconn β Q| + |cdis β Q| ≤ C * β ^ 3 := by sorry

end SYKLearn
