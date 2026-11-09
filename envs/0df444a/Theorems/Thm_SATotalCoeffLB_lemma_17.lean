-- Prove2me | Theorems.Thm_SATotalCoeffLB_lemma_17
-- name    : SATotalCoeffLB.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:17.702805+00:00
-- url     : https://prove2.me/theorems/0a30b9f0-5a49-4d7f-8a55-c49f10230924
-- title:
--   Lemma 17 — the functional $L_0$ on $\mathbb R[X,Y]/\langle y^2-1\rangle$
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$, let $C \subseteq \mathbb F_2^E$ be a linear code, $s \in \{\pm1\}^E$, $L = \{a_z : z \in C\}$ and $\beta(a_z) = s^z$ (a homomorphism $(L,+) \to (\{\pm1\},\cdot)$). Let $0 < \tau < \delta/64$ and assume every nonzero $a \in L$ has $\operatorname{rank}(a) \ge \delta n/16$. Then there is a linear functional $L_0$ on $\mathbb R[X, Y]/\langle y^2 - 1 : y \in X \cup Y\rangle$ with the following properties.
--
--   1. $L_0(1) = 1$.
--   2. For every $\lambda \in L$ and every polynomial $f$, $L_0(f Y^\lambda) = \beta(\lambda) L_0(f)$.
--   3. If $\operatorname{rank}(b) \le \tau n$, then
--   $$
--   L_0(X^\alpha Y^b) = \mathbb E_{\bar x} (-1)^{\alpha\cdot \bar x + b(\bar x)}. \tag{28}
--   $$
--   4. For every pair $e \in \binom{[n]}{2}$ and every monomial $M$ in $X, Y$,
--   $$
--   |L_0(M A_e)| \le \varepsilon, \qquad \varepsilon := 3 \cdot 2^{-\tau n/2}, \tag{29}
--   $$
--   where $A_e = Y_e - \omega_e(X)$.
--
--   $L_0$ is a pseudo-expectation for the AND checks: it enforces $Y^{a_z} = s^z$ for $z \in C$ and is exponentially small on every monomial multiple of an AND check (since $p_e = Y_eA_e/2$). Lemma 19 extends it to the check variables $T$.
--
--   Differences from the source:
--   - generalization: the code $C$ of Lemma 15 on the degree-8 graph of Section 9.1, for sufficiently large $m$, with the rank property supplied by Lemma 16 → any $E$, any linear $C \subseteq \mathbb F_2^E$ and any $\pm1$ signs, with the rank property ($\operatorname{rank}(a_z) \ge \delta n/16$ for nonzero $z \in C$) as a hypothesis; reason: the construction and the proof use only the rank property; Lemma 16 supplies it for the page's data
--   - encoding: $\lambda \in L$ and $\beta(\lambda)$ → $\lambda = a_z$ with $z \in C$, and $\beta(a_z) = s^z$; $Y^\lambda = X^0Y^{a_z}$; reason: the page's definition of $L$ and $\beta$
--   - encoding: a monomial $M$ in $X, Y$ → $X^\alpha Y^b$ for $\alpha \in \mathbb F_2^n$, $b \in Q_n$; reason: every monomial has this form (p.52)
--   - encoding: a linear functional on $\mathbb R[X,Y]/\langle y^2-1\rangle$ → an $\mathbb R$-linear map on functions on the cube of $X \sqcup Y$; reason: the ring model of `CubeFn`
--   - encoding: signs $s_e \in \{\pm 1\}$ → real numbers with $s_e = 1 \lor s_e = -1$; reason: same values
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Lemma 17, p.52 (standing data of Section 9.2, p.52)

import Mathlib
import Definitions.Def_SATotalCoeffLB_monoXY
import Definitions.Def_SATotalCoeffLB_phaseExp
import Definitions.Def_SATotalCoeffLB_qrank
import Definitions.Def_SATotalCoeffLB_formOf
import Definitions.Def_SATotalCoeffLB_signProd
import Definitions.Def_SATotalCoeffLB_Ae

namespace SATotalCoeffLB

/-- **Lemma 17 (the functional `L₀`)**, p.52 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Standing data (p.52): a set `E` of pairs on `[n]`, a code `C ⊆ F₂^E`, signs `s ∈ {±1}^E`,
`L := {a_z : z ∈ C}` and `β(a_z) := s^z`; `0 < τ < δ/64`; and every nonzero `a ∈ L` has
`rank(a) ≥ δn/16` (the conclusion of Lemma 16). Then there is a linear functional `L₀` on
`ℝ[X, Y]/⟨y² − 1 : y ∈ X ∪ Y⟩` such that
1. `L₀(1) = 1`;
2. `L₀(f Y^λ) = β(λ) L₀(f)` for every `λ ∈ L` and every polynomial `f`;
3. `L₀(X^α Y^b) = E_{x̄}(−1)^{α·x̄ + b(x̄)}` whenever `rank(b) ≤ τn` (Eq. (28));
4. `|L₀(M A_e)| ≤ ε := 3·2^{−τn/2}` for every pair `e` and every monomial `M = X^α Y^b`
   (Eq. (29)).

**Formalization Note** The rank property of `L` is a hypothesis (on the page it is Lemma 16 for
the code of Lemma 15 and `m` large). `λ ∈ L` is written `λ = a_z`, `z ∈ C`, and then
`β(λ) = s^z`. -/
theorem lemma_17 (n : ℕ) (E : Finset (Pair n)) (C : Submodule (ZMod 2) (E → ZMod 2))
    (s : E → ℝ) (hs : ∀ e, s e = 1 ∨ s e = -1) (δ τ : ℝ) (hτ : 0 < τ) (hτδ : τ < δ / 64)
    (hrank : ∀ z ∈ C, z ≠ 0 → δ * n / 16 ≤ (qrank (formOf E z) : ℝ)) :
    ∃ L0 : CubeFn (Fin n ⊕ Pair n) →ₗ[ℝ] ℝ,
      L0 1 = 1 ∧
      (∀ z ∈ C, ∀ f : CubeFn (Fin n ⊕ Pair n),
        L0 (f * monoXY 0 (formOf E z)) = signProd s z * L0 f) ∧
      (∀ (α : Fin n → ZMod 2) (b : QForm n), (qrank b : ℝ) ≤ τ * n →
        L0 (monoXY α b) = phaseExp α b) ∧
      ∀ (e : Pair n) (α : Fin n → ZMod 2) (b : QForm n),
        |L0 (monoXY α b * Ae e)| ≤ 3 * (2 : ℝ) ^ (-(τ * n / 2)) := by sorry

end SATotalCoeffLB
