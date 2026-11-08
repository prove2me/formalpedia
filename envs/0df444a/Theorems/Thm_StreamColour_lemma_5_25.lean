-- Prove2me | Theorems.Thm_StreamColour_lemma_5_25
-- name    : StreamColour.lemma_5_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:43.573985+00:00
-- url     : https://prove2.me/theorems/667db3fc-8a69-4717-8eaa-2cd65e636da5
-- title:
--   Lemma 5.25 — with probability $1-5n^{-10}$ the ideal lists contain a proper colouring
-- statement:
--   Let $1\le k<\Delta\le n-1$, $q=\Delta-k$, and let $G$ be an $n$-vertex $q$-colourable graph of maximum degree at most $\Delta$, with $\Delta>C_*h^2$ for sufficiently large constants. Fix an $(\eta,\varepsilon)$-almost-clique decomposition and capacities at least $b_0=K_{\mathrm{rec}}h$ satisfying the conclusion of Lemma 5.23. For the independent samples $\chi(v)\in[q]$ and $t$-element sets $P^1(v),P^2(v)\subseteq[q]$, with $t=\lceil C_{\mathrm{pal}}\ell^2\rceil$, put $P(v)=\{\chi(v)\}\cup P^1(v)\cup P^2(v)$, and let $L^\star(v)=[q]$ for $v\in\mathcal R^\star$ and $L^\star(v)=P(v)$ otherwise. With probability at least $1-5n^{-10}$ there is a proper colouring $\varphi:V(G)\to[q]$ with $\varphi(v)\in L^\star(v)$ for every $v$.
--
--   This is why the lists searched by Algorithm B contain a colouring, and it is where the Molloy–Reed framework enters.
--
--   Differences from the source:
--   - generalization: the single $\eta$ of Proposition 5.2, and $0<\varepsilon<\min\{\varepsilon_0,1/100\}$ → thresholds $\eta_1,\varepsilon_1>0$, and every $\eta\in(0,\eta_1]$ and $\varepsilon\in(0,\min\{\varepsilon_1,1/100\})$; reason: an $(\eta,\varepsilon)$-decomposition is an $(\eta',\varepsilon)$-decomposition for $\eta'\le\eta$, so taking $\eta'=\min\{\eta,\eta_1\}$ joins it to Proposition 5.2; the printed case is a special case, if [FH26b, Lemma 3.4] does not need Definition 5.1(i), which is unchecked
--   - encoding: "Fix a successful decomposition and capacities satisfying Lemma 5.23" → for every labelling and every capacity vector with $b(v)\ge b_0$ for which the conclusion of Lemma 5.23 holds; reason: the capacity law is supported on $b\ge b_0$, and Lemma 5.24 uses it; the samples are independent of them by quantifier order
--   - reading: "sufficiently large" constants, in several places → $\eta,\varepsilon$, then $C_0$ and every $C\ge C_0$, then $A,C_{\mathrm{pal}},K_{\mathrm{rec}},C_{*,0}$, then every $C_*\ge C_{*,0}$; reason: the order of §6, p.85; $A$ depends on $\eta,\varepsilon$ in Lemma 5.9
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Lemma 5.25, p.82 (PDF 84); p.82 for $L^\star$; Step 1, p.75 (PDF 77)

import Mathlib
import Definitions.Def_StreamColour_Params
import Definitions.Def_StreamColour_ACD
import Definitions.Def_StreamColour_Capacity

namespace StreamColour

/-- Chakraborty, Chatterjee, Kundu, Mishra, *Streaming Graph Colouring Meets Molloy–Reed via Kernelization* (STOC 2027 submission, sha256 31a813b3…), Lemma 5.25, p.82 (PDF 84), with the ideal lists of p.82.

**Formalization Note.** "Fix a successful decomposition and capacities satisfying Lemma 5.23" (p.82) is the hypothesis `AnchoredMatchings` at `b`, together with `b(v) ≥ b₀`,
which holds on the whole support of the capacity law and is used in Lemma 5.24. The statement is for every such `π` and `b`, not on average; the colour samples are independent of
them by the order of quantifiers (uniform on the product). `L⋆(v)` is `[q]` on `R⋆` and `P(v)` otherwise, so only `v ∉ R⋆` carries a condition. The constants: `η, ε` first, as the paper's `A` depends
on them (Lemma 5.9), then `C₀` and `C`, then `A, K_rec, C_pal`, then `C_∗`, which is §6's order. Results the proof cites stay out of the statement. -/
theorem lemma_5_25 : ∃ η₁ ε₁ : ℝ, 0 < η₁ ∧ 0 < ε₁ ∧ ∀ η ε : ℝ, 0 < η → η ≤ η₁ → 0 < ε → ε < ε₁ → ε < 1 / 100 →
    ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ (A Cp Cs₀ : ℝ) (Krec : ℕ), ∀ Cs ≥ Cs₀,
    ∀ (n Δ k : ℕ) (G : SimpleGraph (Fin n)) (π : Fin n → ℕ) (b : Fin n → ℕ),
    1 ≤ k → k < Δ → Δ ≤ n - 1 → (∀ v, (G.neighborSet v).ncard ≤ Δ) → G.Colorable (Δ - k) →
    IsACD η ε Δ G π → Cs * (hParam C n k : ℝ) ^ 2 < (Δ : ℝ) →
    (∀ v, Krec * hParam C n k ≤ b v) → AnchoredMatchings A (hParam C n k) Δ G π b →
    1 - 5 / (n : ℝ) ^ 10 ≤ unifProb
      ((Fin n → Fin (Δ - k)) × (Fin n → TSubset (Δ - k) (sampleSize Cp n)) ×
        (Fin n → TSubset (Δ - k) (sampleSize Cp n)))
      (fun ω => ∃ φ : Fin n → Fin (Δ - k), (∀ u v, G.Adj u v → φ u ≠ φ v) ∧
        ∀ v, v ∉ Rstar G π b → φ v = ω.1 v ∨ φ v ∈ (ω.2.1 v).1 ∨ φ v ∈ (ω.2.2 v).1) := by sorry

end StreamColour
