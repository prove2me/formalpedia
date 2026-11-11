-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_25
-- name    : SmallBiasPRF.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:26.992369+00:00
-- url     : https://prove2.me/theorems/dd15b152-9fb5-44bc-b99f-b2165a0f31da
-- title:
--   Lemma 25 — $N_B(S)$ has codimension at least $\mathrm{gap}_B(S)$
-- statement:
--   Let $B\subseteq\mathbb F_2^n$ be nonempty and $S:B\to\mathbb F_3$. If $\mathrm{gap}_B(S)\ge1$, then
--
--   $$\operatorname{codim}_{V_B^*}N_B(S)\ \ge\ \mathrm{gap}_B(S),\qquad\text{equivalently}\qquad \dim N_B(S)\le\deg(Q_{B,S}).$$
--
--   A positive gap therefore forces many functionals outside $N_B(S)$, i.e. many updates that lower the gap.
--
--   **Formalization Note** The statement holds for every basis of $V_B^*$ and every field $K$ of characteristic $2$ containing $\omega$ with $\omega^2+\omega+1=0$; states are total functions read on $B$. The codimension is the dimension of the quotient $V_B^*/N_B(S)$ over $\mathbb F_2$; both forms are stated.
--
--   Differences from the source:
--   - generalization: F₄ = F₂(ω) with ω² + ω + 1 = 0 → any field K with CharP K 2 and an element ω with ω² + ω + 1 = 0; reason: every such K contains the subfield F₂(ω) ≅ F₄, all polynomials involved have coefficients there, and degrees and kernels do not change under the field extension; K = F₄ is the paper's case
--   - reading: “choose a basis X_{B,1}, …, X_{B,D_B} of V_B*” → the statement holds for every basis X : Basis ι (ZMod 2) (Dual V_B), ι any finite index type; reason: the paper fixes an arbitrary basis; the universal reading is the strongest and specializes to any chosen basis indexed by [D_B]
--   - encoding: R_B = F₄[X_{B,1}, …, X_{B,D_B}]/(X²_{B,i} − X_{B,i}) as multilinear polynomials; deg of the zero polynomial is 0; S : B → F₃ → coefficient maps Finset ι → K with product X_J·X_L = X_{J∪L}; deg = largest |I| with nonzero coefficient (0 for the zero polynomial); S a total function F₂ⁿ → ZMod 3 read on B; reason: the multilinear representatives of the quotient ring; same polynomials, products and degrees
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 25, p.30 (PDF 33)

import Mathlib
import Definitions.Def_SmallBiasPRF_statePoly

namespace SmallBiasPRF

/-- **Lemma 25** (codimension of `N_B(S)`), p.30 (PDF p.33).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 25, p.30 (PDF p.33).

If `gap_B(S) ≥ 1`, then `codim_{V_B*} N_B(S) ≥ gap_B(S)`. Equivalently,
`dim N_B(S) ≤ deg(Q_{B,S})`.

**Formalization Note.** \`B ⊆ 𝔽₂ⁿ\` is a nonempty \`Finset\` (the standing "nonempty active set" of §§5.5–5.9) and
the state \`S\` a total function \`𝔽₂ⁿ → ZMod 3\` read on \`B\`. The basis \`X\` of \`V_B*\` is
arbitrary (indexed by any finite type \`ι\`): the statement holds for every basis. \`F₄ = 𝔽₂(ω)\` is
generalized to any field \`K\` of characteristic 2 with \`ω² + ω + 1 = 0\` (every such \`K\` contains
\`𝔽₂(ω) ≅ F₄\`, and all objects are defined over it). Multilinear polynomials are coefficient maps
\`Finset ι → K\`; the zero polynomial has degree \`0\`. The codimension is `finrank (V_B* ⧸ N_B(S))` over `𝔽₂`. Both forms
are stated. -/
theorem lemma_25 (n : ℕ) [NeZero n] (B : Finset (Fin n → ZMod 2)) (hB : B.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    {K : Type*} [Field K] [CharP K 2] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (S : (Fin n → ZMod 2) → ZMod 3) (hgap : 1 ≤ gap X ω S) :
    gap X ω S ≤ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (VB B) ⧸ Nspace X ω S) ∧
      Module.finrank (ZMod 2) (Nspace X ω S) ≤ (statePoly X ω S).deg := by sorry

end SmallBiasPRF
