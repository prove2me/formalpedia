-- Prove2me | Theorems.Thm_PrivPCP_lemma_6_2
-- name    : PrivPCP.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:45.153401+00:00
-- url     : https://prove2.me/theorems/1781b6c1-10a9-4231-bef8-ad5486e291f3
-- title:
--   Lemma 6.2: joint privacy of Nullstellensatz certificates
-- statement:
--   Work on grids $D=\prod_iH_i$ and $\Omega=\prod_iS_i$ in $\mathbb F_q^k$, $k\ge2$, with $h_i=|H_i|\ge1$, $H_i\cap S_i=\emptyset$ and a degree profile $h_i\le a_i<s_i$, and with the nested codes of §4.1. Let $C$ be a constant such that every $M\in\mathbb F_q^\Omega$ satisfies the relative robust testability inequality of Corollary 4.4,
--   $$\mathrm{dist}(M,K^\perp)\le C\sum_{i=1}^k\mathrm{dist}(M,D_i).$$
--   For each message $m$ let $G(m)\in Z_a$ be a random polynomial whose law may depend on $m$, and conditioned on $G(m)$ let $\mathrm{NS}(G(m))=(Q_1,\dots,Q_k)$ be uniform among the tuples $Q_i\in Q_i(a)$ with $G(m)=\sum_iZ_iQ_i$. Suppose that for every $T\subseteq\Omega$ with $|T|\le s$ the law of $G(m)|_T$ is the same for every message $m$. If $T_G,T_1,\dots,T_k\subseteq\Omega$ satisfy
--   $$|T_G|+C\sum_{i=1}^k|T_i|\le s,$$
--   then the law of
--   $$\big(G(m)|_{T_G},\ Q_1|_{T_1},\ \dots,\ Q_k|_{T_k}\big)$$
--   is the same for every message $m$.
--
--   Adjoining a uniformly random Nullstellensatz certificate reveals no more than a somewhat larger local view of the certified polynomial; this is the step of the joint-privacy proof (Lemma 6.3) that handles the prover-supplied certificates.
--
--   **Formalization Note** Polynomials are identified with their evaluation vectors on $\Omega$, which is injective under $a_i<s_i$.
--
--   Differences from the source:
--   - generalization: the hypotheses of Corollary 4.4 for the degree profile $a$, and $C=C(\rho,k)$ from that corollary → §4.1's standing assumptions and any constant $C$ satisfying Corollary 4.4's inequality for these codes; reason: the proof uses Corollary 4.4 only through this inequality, (35); under the paper's hypotheses $C(\rho,k)$ satisfies it
--   - generalization: messages $m\in\mathbb F_q^D$, $q$ prime → messages of any type, any finite field; reason: neither is used; the paper's case is an instance
--   - encoding: polynomials $G(m)$, $Q_i$ and their restrictions → evaluation vectors on $\Omega$; the certificate law is uniform on evaluation tuples; reason: evaluation is injective on $P_a$ and on each $Q_i(a)$ (the paper's own identification, p.36)
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Lemma 6.2, p.37 (PDF p.39); §6.2 set-up, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_PrivPCP_rsNested
import Definitions.Def_PrivPCP_certLaw

namespace PrivPCP

/-- **Lemma 6.2 (Joint privacy of Nullstellensatz certificates)** (Bafna, Vyas, *Private PCPs from Product
Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Lemma 6.2, p.37, with the set-up of §6.2, p.36).
In the §4.1 set-up on grids `D = ∏_i H_i`, `Ω = ∏_i S_i` with degree profile `a`, let `C` be a constant with
`dist(M, K^⊥) ⩽ C ∑_i dist(M, D_i)` for every `M` (Corollary 4.4's relative robust testability). For each
message `m`, let `G(m) ∈ Z_a` be a random polynomial, and conditioned on `G(m)` let `(Q_1, …, Q_k)` be a uniform
degree-bounded certificate with `G(m) = ∑_i Z_i Q_i`. Suppose that for every `T ⊆ Ω` with `|T| ⩽ s` the law of
`G(m)|_T` is the same for every message `m`. If `T_G, T_1, …, T_k ⊆ Ω` satisfy
`|T_G| + C ∑_i |T_i| ⩽ s`, then the law of `(G(m)|_{T_G}, Q_1|_{T_1}, …, Q_k|_{T_k})` is the same for every `m`.

**Formalization Note** Polynomials are identified with their evaluation vectors on `Ω` (§6.2: "We identify
polynomials with their evaluation vectors on `Ω`"), injective under `a_i < s_i`. The paper takes the hypotheses
of Corollary 4.4 and `C = C(ρ, k)` from that corollary; here `C` is any constant satisfying Corollary 4.4's
inequality for this degree profile, together with §4.1's standing assumptions `h_i ⩾ 1`, `H_i ∩ S_i = ∅`,
`h_i ⩽ a_i < s_i`. Messages range over any type and `𝔽_q` is any finite field. -/
theorem lemma_6_2 {F : Type} [Field F] [Fintype F] {k : ℕ} (hk : 2 ≤ k) (S H : Fin k → Finset F)
    (a : Fin k → ℕ)
    (hSH : ∀ i, 1 ≤ (H i).card ∧ Disjoint (H i) (S i) ∧ (H i).card ≤ a i ∧ a i < (S i).card)
    (C : ℝ) (hC : ∀ M : Grid S → F,
      (distTo M (rsNested S H a).Dbig : ℝ) ≤ C * ∑ i, (distTo M ((rsNested S H a).D i) : ℝ))
    {Msg : Type} (G : Msg → PMF (Grid S → F)) (hG : ∀ m, ∀ g ∈ (G m).support, g ∈ zaEval S H a)
    (s : ℕ) (hpriv : ∀ T : Finset (Grid S), T.card ≤ s → ∀ m m',
      (G m).map (fun g (x : T) => g x) = (G m').map (fun g (x : T) => g x))
    (TG : Finset (Grid S)) (T : Fin k → Finset (Grid S))
    (hT : (TG.card : ℝ) + C * ∑ i, ((T i).card : ℝ) ≤ s) (m m' : Msg) :
    (jointCertLaw S H a (G m)).map (fun p => ((fun x : TG => p.1 x), fun i (x : T i) => p.2 i x)) =
      (jointCertLaw S H a (G m')).map (fun p => ((fun x : TG => p.1 x), fun i (x : T i) => p.2 i x)) := by sorry

end PrivPCP
