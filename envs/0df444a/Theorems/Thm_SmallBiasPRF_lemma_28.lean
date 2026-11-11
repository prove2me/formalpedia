-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_28
-- name    : SmallBiasPRF.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:35.251214+00:00
-- url     : https://prove2.me/theorems/d2b2579c-8198-447b-b47d-d092bdff6e79
-- title:
--   Lemma 28 — at most $9m_1/16$ code coordinates are bad updates
-- statement:
--   Let $H:\mathbb F_2^n\to\mathbb F_2^{m_1}$ be a linear code of minimum relative distance at least $7/16$, $B\subseteq\mathbb F_2^n$ nonempty and $S:B\to\mathbb F_3$. If $\mathrm{gap}_B(S)\ge1$, then
--
--   $$\big|\{x\in\Omega:\ P_{\tilde U_x|_B}\in N_B(S)\}\big|\ \le\ \frac{9m_1}{16},$$
--
--   equivalently at least $7m_1/16$ of the (restricted) code-coordinate updates lie outside $N_B(S)$. Here $P_{\tilde U_x|_B}$ is the functional $v\mapsto H(v)_x$ on $V_B$.
--
--   This is where the distance of $H$ enters: the code-generated update multiset is good on average, which is the hypothesis of Lemma 29.
--
--   **Formalization Note** The statement holds for every basis of $V_B^*$ and every field $K$ of characteristic $2$ containing $\omega$ with $\omega^2+\omega+1=0$; states are total functions read on $B$. Both counts are stated, multiplied by $16$.
--
--   Differences from the source:
--   - generalization: F₄ = F₂(ω) with ω² + ω + 1 = 0 → any field K with CharP K 2 and an element ω with ω² + ω + 1 = 0; reason: every such K contains the subfield F₂(ω) ≅ F₄, all polynomials involved have coefficients there, and degrees and kernels do not change under the field extension; K = F₄ is the paper's case
--   - reading: “choose a basis X_{B,1}, …, X_{B,D_B} of V_B*” → the statement holds for every basis X : Basis ι (ZMod 2) (Dual V_B), ι any finite index type; reason: the paper fixes an arbitrary basis; the universal reading is the strongest and specializes to any chosen basis indexed by [D_B]
--   - encoding: R_B = F₄[X_{B,1}, …, X_{B,D_B}]/(X²_{B,i} − X_{B,i}) as multilinear polynomials; deg of the zero polynomial is 0; S : B → F₃ → coefficient maps Finset ι → K with product X_J·X_L = X_{J∪L}; deg = largest |I| with nonzero coefficient (0 for the zero polynomial); S a total function F₂ⁿ → ZMod 3 read on B; reason: the multilinear representatives of the quotient ring; same polynomials, products and degrees
--   - encoding: H a linear code of minimum relative distance at least 7/16 → H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2) with (7/16)·m₁ ≤ wt(H v) for all v ≠ 0 (HasMinRelDist); reason: for a linear code the minimum distance is the minimum weight of a nonzero codeword; same instances
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 28, p.32 (PDF 35)

import Mathlib
import Definitions.Def_SmallBiasPRF_HasMinRelDist
import Definitions.Def_SmallBiasPRF_statePoly

namespace SmallBiasPRF

/-- **Lemma 28** (limited bad code-coordinate updates), p.32 (PDF p.35).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 28, p.32 (PDF p.35).

Let `H : 𝔽₂ⁿ → 𝔽₂^{m₁}` be a linear code of minimum relative distance at least `7/16` (standing
from Theorem 6). If `gap_B(S) ≥ 1`, then `|{x ∈ Ω : P_{Ũ_x|_B} ∈ N_B(S)}| ≤ 9m₁/16`.
Equivalently, at least `7m₁/16` (restricted) code-coordinate polynomial updates lie outside
`N_B(S)`.

**Formalization Note.** \`B ⊆ 𝔽₂ⁿ\` is a nonempty \`Finset\` (the standing "nonempty active set" of §§5.5–5.9) and
the state \`S\` a total function \`𝔽₂ⁿ → ZMod 3\` read on \`B\`. The basis \`X\` of \`V_B*\` is
arbitrary (indexed by any finite type \`ι\`): the statement holds for every basis. \`F₄ = 𝔽₂(ω)\` is
generalized to any field \`K\` of characteristic 2 with \`ω² + ω + 1 = 0\` (every such \`K\` contains
\`𝔽₂(ω) ≅ F₄\`, and all objects are defined over it). Multilinear polynomials are coefficient maps
\`Finset ι → K\`; the zero polynomial has degree \`0\`. `P_{Ũ_x|_B}` is the functional `v ↦ H(v)_x` on `V_B`
(`codeFunctional`). Both counts are stated, multiplied out by 16 in `ℕ`. -/
theorem lemma_28 (n m₁ : ℕ) [NeZero n] [NeZero m₁]
    (H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m₁ → ZMod 2)) (hH : HasMinRelDist H (7 / 16))
    (B : Finset (Fin n → ZMod 2)) (hB : B.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    {K : Type*} [Field K] [CharP K 2] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (S : (Fin n → ZMod 2) → ZMod 3) (hgap : 1 ≤ gap X ω S) :
    16 * {x : Fin m₁ | codeFunctional H B x ∈ Nspace X ω S}.ncard ≤ 9 * m₁ ∧
      7 * m₁ ≤ 16 * {x : Fin m₁ | codeFunctional H B x ∉ Nspace X ω S}.ncard := by sorry

end SmallBiasPRF
