-- Prove2me | Theorems.Thm_SmallBiasPRF_lemma_18
-- name    : SmallBiasPRF.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:27.180507+00:00
-- url     : https://prove2.me/theorems/5bb7daa8-4d29-491c-9628-43222e455edf
-- title:
--   Lemma 18 — the degree of $Q_{B,S}$ detects contraction
-- statement:
--   Let $B\subseteq\mathbb F_2^n$ be nonempty. For every state $S:B\to\mathbb F_3$,
--
--   $$\deg(Q_{B,S})<D_B\iff \mathrm{gap}_B(S)\ge1\iff S\ \text{is noncontracting}.$$
--
--   The point-function polynomial thus encodes the contraction behaviour of a state in its top coefficient, which is what allows the gap to serve as a potential.
--
--   **Formalization Note** The statement holds for every basis of $V_B^*$ and every field $K$ of characteristic $2$ containing $\omega$ with $\omega^2+\omega+1=0$; states are total functions read on $B$.
--
--   Differences from the source:
--   - generalization: F₄ = F₂(ω) with ω² + ω + 1 = 0 → any field K with CharP K 2 and an element ω with ω² + ω + 1 = 0; reason: every such K contains the subfield F₂(ω) ≅ F₄, all polynomials involved have coefficients there, and degrees and kernels do not change under the field extension; K = F₄ is the paper's case
--   - reading: “choose a basis X_{B,1}, …, X_{B,D_B} of V_B*” → the statement holds for every basis X : Basis ι (ZMod 2) (Dual V_B), ι any finite index type; reason: the paper fixes an arbitrary basis; the universal reading is the strongest and specializes to any chosen basis indexed by [D_B]
--   - encoding: R_B = F₄[X_{B,1}, …, X_{B,D_B}]/(X²_{B,i} − X_{B,i}) as multilinear polynomials; deg of the zero polynomial is 0; S : B → F₃ → coefficient maps Finset ι → K with product X_J·X_L = X_{J∪L}; deg = largest |I| with nonzero coefficient (0 for the zero polynomial); S a total function F₂ⁿ → ZMod 3 read on B; reason: the multilinear representatives of the quotient ring; same polynomials, products and degrees
-- source:
--   Dinur–Ishai, Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with Exponentially Small Bias, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 18, p.26 (PDF 29)

import Mathlib
import Definitions.Def_SmallBiasPRF_Lambda
import Definitions.Def_SmallBiasPRF_statePoly

namespace SmallBiasPRF

/-- **Lemma 18** (the polynomial encodes contraction), p.26 (PDF p.29).
Dinur–Ishai, *Towards Asymptotically Optimal Pseudorandom Functions: Linear-Size Circuits with
Exponentially Small Bias*, STOC 2027 submission (version of 2026-11-03, sha256 65dbd47e…), Lemma 18, p.26 (PDF p.29).

For every state `S : B → 𝔽₃`,
`deg(Q_{B,S}) < D_B ⟺ gap_B(S) ≥ 1 ⟺ S is noncontracting`.

**Formalization Note.** \`B ⊆ 𝔽₂ⁿ\` is a nonempty \`Finset\` (the standing "nonempty active set" of §§5.5–5.9) and
the state \`S\` a total function \`𝔽₂ⁿ → ZMod 3\` read on \`B\`. The basis \`X\` of \`V_B*\` is
arbitrary (indexed by any finite type \`ι\`): the statement holds for every basis. \`F₄ = 𝔽₂(ω)\` is
generalized to any field \`K\` of characteristic 2 with \`ω² + ω + 1 = 0\` (every such \`K\` contains
\`𝔽₂(ω) ≅ F₄\`, and all objects are defined over it). Multilinear polynomials are coefficient maps
\`Finset ι → K\`; the zero polynomial has degree \`0\`. `D_B` is `finrank V_B`. -/
theorem lemma_18 (n : ℕ) [NeZero n] (B : Finset (Fin n → ZMod 2)) (hB : B.Nonempty)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Module.Basis ι (ZMod 2) (Module.Dual (ZMod 2) (VB B)))
    {K : Type*} [Field K] [CharP K 2] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (S : (Fin n → ZMod 2) → ZMod 3) :
    ((statePoly X ω S).deg < Module.finrank (ZMod 2) (VB B) ↔ 1 ≤ gap X ω S) ∧
      (1 ≤ gap X ω S ↔ IsNoncontracting B S) := by sorry

end SmallBiasPRF
