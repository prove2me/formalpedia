-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_24
-- name    : SmallBiasPRF.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:33.65966+00:00
-- url     : https://prove2.me/theorems/5d664068-41a1-4ed3-beaf-5e9bd117239e
-- title:
--   Lemma 24 — how a linear update changes the gap
-- statement:
--   Let $B\subseteq\mathbb F_2^n$ be nonempty, $S:B\to\mathbb F_3$, let $U$ be a linear update and $\rho\in\{1,2\}\subseteq\mathbb F_3$.
--
--   1. If $P_U\notin N_B(S)$, then $\mathrm{gap}_B(S+\rho U)=\mathrm{gap}_B(S)-1$.
--   2. If $P_U\in N_B(S)$, then $\mathrm{gap}_B(S+\rho U)\in\{\mathrm{gap}_B(S),\ \mathrm{gap}_B(S)+1\}$.
--   3. The gap can increase for at most one value of $\rho\in\{1,2\}$.
--
--   This is the single-step dynamics of the potential $\Psi_B=(4/3)^{\mathrm{gap}_B}$ used in Lemma 29.
--
--   **Formalization Note** The statement holds for every basis of $V_B^*$ and every field $K$ of characteristic $2$ containing $\omega$ with $\omega^2+\omega+1=0$; states are total functions read on $B$. The first clause is stated as $\mathrm{gap}_B(S+\rho U)+1=\mathrm{gap}_B(S)$.
--
--   Differences from the source:
--   - generalization: F₄ = F₂(ω) with ω² + ω + 1 = 0 → any field K with CharP K 2 and an element ω with ω² + ω + 1 = 0; reason: every such K contains the subfield F₂(ω) ≅ F₄, all polynomials involved have coefficients there, and degrees and kernels do not change under the field extension; K = F₄ is the paper's case
--   - reading: “choose a basis X_{B,1}, …, X_{B,D_B} of V_B*” → the statement holds for every basis X : Basis ι (ZMod 2) (Dual V_B), ι any finite index type; reason: the paper fixes an arbitrary basis; the universal reading is the strongest and specializes to any chosen basis indexed by [D_B]
--   - encoding: R_B = F₄[X_{B,1}, …, X_{B,D_B}]/(X²_{B,i} − X_{B,i}) as multilinear polynomials; deg of the zero polynomial is 0; S : B → F₃ → coefficient maps Finset ι → K with product X_J·X_L = X_{J∪L}; deg = largest |I| with nonzero coefficient (0 for the zero polynomial); S a total function F₂ⁿ → ZMod 3 read on B; reason: the multilinear representatives of the quotient ring; same polynomials, products and degrees
--   - encoding: a linear update U : B → F₂ (extends to a functional in V_B*) and its linear polynomial P_U → the update is given by its extension L ∈ V_B* (updOfDual L), and P_U ∈ N_B(S) is L ∈ Nspace X ω S; reason: the extension is unique because B spans V_B, so linear updates and functionals correspond bijectively on B
--   - encoding: gap_B(S + ρU) = gap_B(S) − 1 (integers) → gap (S + ρU) + 1 = gap S (natural numbers); reason: avoids truncated subtraction; the integer equation is the same statement and implies gap_B(S) ≥ 1
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 24, p.29 (PDF 32)

import Mathlib
import Definitions.Def_SmallBiasPRF_statePoly

namespace SmallBiasPRF

/-- **Lemma 24** (gap under a linear update), p.29 (PDF p.32).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 24, p.29 (PDF p.32).

Let `U` be a linear update and let `ρ ∈ {1, 2} ⊆ 𝔽₃`. If `P_U ∉ N_B(S)`, then
`gap_B(S + ρU) = gap_B(S) − 1`. If `P_U ∈ N_B(S)`, then
`gap_B(S + ρU) ∈ {gap_B(S), gap_B(S) + 1}`. Moreover, the gap can increase for at most one value
of `ρ ∈ {1, 2}`.

**Formalization Note.** \`B ⊆ 𝔽₂ⁿ\` is a nonempty \`Finset\` (the standing "nonempty active set" of §§5.5–5.9) and
the state \`S\` a total function \`𝔽₂ⁿ → ZMod 3\` read on \`B\`. The basis \`X\` of \`V_B*\` is
arbitrary (indexed by any finite type \`ι\`): the statement holds for every basis. \`F₄ = 𝔽₂(ω)\` is
generalized to any field \`K\` of characteristic 2 with \`ω² + ω + 1 = 0\` (every such \`K\` contains
\`𝔽₂(ω) ≅ F₄\`, and all objects are defined over it). Multilinear polynomials are coefficient maps
\`Finset ι → K\`; the zero polynomial has degree \`0\`. The linear update `U` is given by its (unique) extension
`L ∈ V_B*` (`updOfDual L`), so `P_U ∈ N_B(S)` is `L ∈ Nspace X ω S`. With `gap` in `ℕ`, the first
clause is written `gap(S + ρU) + 1 = gap(S)` (this includes `gap(S) ≥ 1`). "At most one `ρ`" is:
not both `gap(S + U) > gap(S)` and `gap(S + 2U) > gap(S)`. -/
theorem lemma_24 (n : ℕ) [NeZero n] (B : Finset (Fin n → ZMod 2)) (hB : B.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    {K : Type*} [Field K] [CharP K 2] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (S : (Fin n → ZMod 2) → ZMod 3) (L : Module.Dual (ZMod 2) (VB B)) :
    (∀ ρ : ZMod 3, ρ ≠ 0 →
        (L ∉ Nspace X ω S → gap X ω (addUpd S ρ (updOfDual L)) + 1 = gap X ω S) ∧
        (L ∈ Nspace X ω S →
          gap X ω (addUpd S ρ (updOfDual L)) = gap X ω S ∨
            gap X ω (addUpd S ρ (updOfDual L)) = gap X ω S + 1)) ∧
      ¬ (gap X ω S < gap X ω (addUpd S 1 (updOfDual L)) ∧
          gap X ω S < gap X ω (addUpd S 2 (updOfDual L))) := by sorry

end SmallBiasPRF
